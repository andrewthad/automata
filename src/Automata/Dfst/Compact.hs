{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}

module Automata.Dfst.Compact
  ( -- * Types
    CompactDfst
  , Indexed(..)
  , Ranged(..)
    -- * Functions
  , compact
  , evaluateList
  , toDot
    -- * Properties
  , states
  ) where

import Prelude hiding (map)

import Automata.Internal (State(..),Dfsa(..),composeMapping)
import Automata.Internal.Transducer (CompactDfst(..),Dfst(..),MotionDfst(..),Edge(..),EdgeDest(..),CompactSequence(..),TransitionCompactDfst(..))
import Control.Applicative (liftA2)
import Control.Monad.ST (runST)
import Control.Monad (forM_)
import Data.Foldable (foldl',for_)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe,isJust)
import Data.Primitive (Array,indexArray,sizeofArray)
import Data.Semigroup (Last(..))
import Data.Set (Set)
import Data.ByteString (ByteString)
import Data.Bool (bool)
import Data.Monoid (Sum(..))
import Data.Foldable (foldlM)
import Control.Monad.Trans.State.Strict (get,put,runState)

import qualified Data.ByteString.Char8 as BC
import qualified Data.DisjointMap as DJM
import qualified Data.List as L
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Strict as M
import qualified Data.Primitive as P
import qualified Data.Primitive as PM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set as S
import qualified Data.Set.Unboxed as SU
import qualified GHC.Exts as E

data Indexed m = Indexed !Int m
data Ranged m = Ranged
  { rangedIndex :: !Int
  , rangedLength :: !Int
  , rangedValue :: !m
  } deriving (Eq,Show)

newtype M k v = M (Map k v)

instance (Ord k, Semigroup v) => Semigroup (M k v) where
  M x <> M y = M (M.unionWith (<>) x y)

instance (Ord k, Semigroup v) => Monoid (M k v) where
  mempty = M M.empty

-- | The number of states. Since a 'CompactDfst' is not backed
-- by a true graph (rather, a graph-like structure), this
-- number lacks a good theoretical foundation, but it is still
-- a useful approximation of the size.
states :: CompactDfst t m -> Int
states (CompactDfst t _) = P.sizeofArray t

-- Implementation of compact: We figure out how we want to map old
-- states to new states. Then, we perform the substitution, deleting
-- states that are no longer needed. Transitions should not be
-- affected. That is, every state that survives (e.g. those that
-- become TransitionCompactDfstMultiple and not TransitionCompactDfstSingle)
-- will end with a transition map of the same size.
--
-- TODO: I think it might be alright to allow the start state to
-- become part of a sequence. Supporting this very minor optimization
-- requires some more thought, so I'm not sure if it will ever
-- be done.

compact :: forall t m. (Eq m, Enum t, Ord t, Bounded t)
  => Dfst t m
  -> CompactDfst t m
compact (Dfst transitions finals) =
  let -- How many transitions there are from other nodes to each node.
      -- We are interested in cases where this number is one.
      entryCounts :: M.Map Int (Sum Int)
      M entryCounts = C.foldlMap' (foldMap (M . flip M.singleton (Sum 1) . motionDfstState) . DM.elems) transitions
      _xs :: (DJM.DisjointMap Int ([t],Last Int),M.Map Int (MotionDfst m, MotionDfst m))
      _xs@(collapse0,singles) = C.ifoldlMap1'
        (\ix m -> case DM.toList m of
          _ | SU.member ix finals || ix == 0 -> (DJM.empty,M.empty)
          [(_,_,x),(lo,hi,v),(_,_,w)] | lo == hi && x == w -> (DJM.singleton ix ([lo],Last (motionDfstState v)),M.singleton ix (v,w))
          [(lo,hi,v),(_,_,w)] | lo == hi -> (DJM.singleton ix ([lo],Last (motionDfstState v)),M.singleton ix (v,w))
          [(_,_,w),(lo,hi,v)] | lo == hi -> (DJM.singleton ix ([lo],Last (motionDfstState v)),M.singleton ix (v,w))
          -- [(lo,hi,v)] | lo == hi -> (DJM.singleton ix [lo],M.singleton ix v)
          _ -> (DJM.empty,M.empty)
        ) transitions
      collapseFinal = M.foldlWithKey'
        (\collapse src (MotionDfst srcSuccessState srcSuccessOutput,MotionDfst srcFailureState srcFailureOutput) ->
          let dst = srcSuccessState in
          case M.lookup dst singles of
            Nothing -> collapse
            Just (MotionDfst _ dstSuccessOutput,MotionDfst dstFailureState dstFailureOutput) ->
              if dstSuccessOutput == srcSuccessOutput && srcFailureState == dstFailureState && srcFailureOutput == dstFailureOutput && M.lookup dst entryCounts == Just (Sum 1)
                then DJM.unionWeakly src dst collapse
                else collapse
        ) collapse0 singles
      ((oldToNew,newToOld),totalStates) = flip runState 1 $ do
        m1 <- foldlM
          (\m (olds,_) -> do
            new <- get
            put (new + 1)
            pure (foldMap (\old -> (M.singleton old new, M.singleton new old)) olds <> m)
          )
          (M.singleton 0 0, M.singleton 0 0)
          (DJM.toLists collapseFinal)
        foldlM
          (\(oldToNew,newToOld) old -> if old == 0 || isJust (M.lookup old (fst m1))
            then pure (oldToNew,newToOld)
            else do
              new <- get
              put (new + 1)
              pure (M.insert old new oldToNew, M.insert new old newToOld)
          ) m1 (enumFromTo 0 (PM.sizeofArray transitions - 1))
      newTransitions = runST $ do
        states <- C.new totalStates
        forM_ (enumFromTo 0 (totalStates - 1)) $ \ix -> do
          let ixOld = newToOld M.! ix
          case DJM.lookup' ixOld collapseFinal of
            Nothing -> do
              PM.writeArray states ix $ TransitionCompactDfstMultiple
                $ DM.map (\(MotionDfst s out) -> MotionDfst (oldToNew M.! s) out)
                $ PM.indexArray transitions ixOld
            Just (string@(_ : _), Last successStateOld) -> do
              PM.writeArray states ix $ TransitionCompactDfstSingle $ CompactSequence
                (E.fromList string)
                (oldToNew M.! successStateOld)
                (oldToNew M.! (motionDfstState (snd (singles M.! ixOld))))
                (motionDfstOutput (fst (singles M.! ixOld)))
                (motionDfstOutput (snd (singles M.! ixOld)))
        PM.unsafeFreezeArray states
      newFinals = SU.fromList (L.map (fromMaybe (error "Automata.Dfst.Compact.compact") . flip M.lookup oldToNew) (SU.toList finals))
   in CompactDfst newTransitions newFinals

evaluateList :: forall t m. (Ord t, Eq m)
  => CompactDfst t m
  -> [t]
  -> Maybe (Array (Ranged m))
evaluateList (CompactDfst transitions finals) tokensX = case tokensX of
  [] -> bool Nothing (Just mempty) (SU.member 0 finals)
  token0 : tokens0 -> case PM.indexArray transitions 0 of
    TransitionCompactDfstSingle (CompactSequence string successState failureState successToken failureToken) ->
      if PM.indexArray string 0 == token0
        -- Sequences are guaranteed to have length >= 1, so this indexing does
        -- not need to be guarded.
        then goSequence string 1 (PM.sizeofArray string) successState failureState failureToken 1 0 successToken 0 [] tokens0
        else goUnknown failureState 1 0 failureToken 0 [] tokens0
    TransitionCompactDfstMultiple theMap ->
      let MotionDfst nextState outputToken = DM.lookup token0 theMap
       in goUnknown nextState 1 0 outputToken 0 [] tokens0
  where
  goSequence :: Array t -> Int -> Int -> Int -> Int -> m -> Int -> Int -> m -> Int -> [Ranged m] -> [t] -> Maybe (Array (Ranged m))
  goSequence !string !stringIx !stringSz !successState !failureState !failureToken !ix !outputSz !nextOutputToken !nextOutputStart !output !tokensA = case tokensA of
    [] -> if stringIx < stringSz
      -- Sequences may not contain final states, so mid-sequence input
      -- termination always indicates an unrecognized input.
      then Nothing
      else if SU.member successState finals
        then let !r = Ranged nextOutputStart (ix - nextOutputStart) nextOutputToken
              in Just $! C.unsafeFromListReverseN (outputSz + 1) (r : output)
        else Nothing
    tokenB : tokensB -> if stringIx < stringSz
      then if PM.indexArray string stringIx == tokenB
        then goSequence string (stringIx + 1) stringSz successState failureState failureToken (ix + 1) outputSz nextOutputToken nextOutputStart output tokensB
        else bool
          (let !r = Ranged nextOutputStart (ix - nextOutputStart) nextOutputToken
            in goUnknown failureState (ix + 1) (outputSz + 1) failureToken ix (r : output) tokensB
          )
          (goUnknown failureState (ix + 1) outputSz failureToken nextOutputStart output tokensB)
          (shortcutEquality nextOutputToken failureToken)
      else goUnknown successState ix outputSz nextOutputToken nextOutputStart output (tokenB : tokensB)
  goUnknown :: Int -> Int -> Int -> m -> Int -> [Ranged m] -> [t] -> Maybe (Array (Ranged m))
  goUnknown !state !ix !outputSz !nextOutputToken !nextOutputStart !output !tokensA = case tokensA of
    [] -> if SU.member state finals
      then let !r = Ranged nextOutputStart (ix - nextOutputStart) nextOutputToken
            in Just $! C.unsafeFromListReverseN (outputSz + 1) (r : output)
      else Nothing
    tokenB : tokensB -> case PM.indexArray transitions state of
      TransitionCompactDfstSingle (CompactSequence string successState failureState successToken failureToken) ->
        if PM.indexArray string 0 == tokenB
          -- Sequences are guaranteed to have length >= 1, so this indexing does
          -- not need to be guarded.
          then bool
            (let !r = Ranged nextOutputStart (ix - nextOutputStart) nextOutputToken
              in goSequence string 1 (PM.sizeofArray string) successState failureState failureToken (ix + 1) (outputSz + 1) successToken ix (r : output) tokensB
            )
            (goSequence string 1 (PM.sizeofArray string) successState failureState failureToken (ix + 1) outputSz successToken nextOutputStart output tokensB)
            (shortcutEquality nextOutputToken successToken)
          else bool
            (let !r = Ranged nextOutputStart (ix - nextOutputStart) nextOutputToken
              in goUnknown failureState (ix + 1) (outputSz + 1) failureToken ix (r : output) tokensB
            )
            (goUnknown failureState (ix + 1) outputSz failureToken nextOutputStart output tokensB)
            (shortcutEquality nextOutputToken failureToken)
      TransitionCompactDfstMultiple theMap ->
        let MotionDfst nextState outputToken = DM.lookup tokenB theMap
         in bool
              (let !r = Ranged nextOutputStart (ix - nextOutputStart) nextOutputToken
                in goUnknown nextState (ix + 1) (outputSz + 1) outputToken ix (r : output) tokensB
              )
              (goUnknown nextState (ix + 1) outputSz outputToken nextOutputStart output tokensB)
              (shortcutEquality nextOutputToken outputToken)

shortcutEquality :: Eq m => m -> m -> Bool
{-# INLINE shortcutEquality #-}
shortcutEquality = (==)

-- -- | Returns the outputs as well as the position at which they were produced.
-- evaluate :: (Foldable f, Ord t, Eq m)
--   => CompactDfst t m
--   -> f t
--   -> Maybe (Array (Ranged m))
-- evaluate (CompactDfst transitions finals) tokens =
--   let !(!finalState,!totalSize,!allOutput) = foldl'
--         (\(!ectx,!ix,!output) token -> case ectx of
--           Right (Indexed singleIx (CompactSequence string successState failureState _ failureOutput)) ->
--             if singleIx < PM.sizeofArray string
--               then if PM.indexArray string ix == token
--                 then
--                   let !indexedOutputToken = Indexed ix _
--                    in (Left failureState,ix + 1,indexedOutputToken : output)
--                 else
--               else case PM.indexArray transitions successState of
--                 
--           Left active -> case PM.indexArray transitions active of
--             TransitionCompactDfstSingle theSeq@(CompactSequence string _ failureState successToken failureToken) ->
--               -- We are only in a Left on the first character of a compact sequence.
--               -- Sequences are guaranteed to have length >= 1, so this indexing does
--               -- not need to be guarded.
--               if PM.indexArray string 0 == token
--                 then 
--                   let !indexedOutputToken = Indexed ix failureToken
--                    in (Left failureState,ix + 1,indexedOutputToken : output)
--                 else
--                   let !indexedOutputToken = Indexed ix successToken
--                    in (Right (Indexed 1 theSeq),ix + 1,indexedOutputToken : output)
--             TransitionCompactDfstMultiple m -> 
--               let MotionDfst nextState outputToken = DM.lookup token m
--                   !indexedOutputToken = Indexed ix outputToken
--                in (Left nextState,ix + 1,indexedOutputToken : output)
--         ) (0,0,[]) tokens
--    in if SU.member finalState finals
--         then Just (C.unsafeFromListReverseN totalSize allOutput)
--         else Nothing
-- 
-- stepToken :: Either 

toDot :: (Bounded t, Enum t)
  => ([t] -> m -> String) -- ^ Label a sequence
  -> (t -> t -> m -> String) -- ^ Label a range
  -> CompactDfst t m
  -> String
toDot makeSequenceLabel makeLabel (CompactDfst ts fs) = concat $
  [ "digraph D {\n" ]
  ++
  dotNodes (sizeofArray ts - 1) fs
  ++
  (do (src,m) <- zip (enumFrom (0 :: Int)) (E.toList ts)
      case m of
        TransitionCompactDfstMultiple motions ->
          dotSourceEdges makeLabel src motions
        TransitionCompactDfstSingle (CompactSequence inputs successState failureState successOutput failureOutput) ->
          [ "  N" ++ show src ++ " -> N" ++ show successState ++ " [label=\"" ++ escapeQuotes (makeSequenceLabel (E.toList inputs) successOutput) ++ "\"];\n"
          , "  N" ++ show src ++ " -> N" ++ show failureState ++ " [label=\"" ++ escapeQuotes (makeSequenceLabel [] failureOutput) ++ "\"];\n"
          ]
  )
  ++
  [ "}\n" ]

dotNodes :: Int -> SU.Set Int -> [String]
dotNodes n fs = if n >= 0
  then ("  N" ++ show n ++ " [shape=" ++ (if SU.member n fs then "circle" else "square") ++ "];\n") : dotNodes (n - 1) fs
  else []

dotSourceEdges :: (Bounded t, Enum t) => (t -> t -> m -> String) -> Int -> DM.Map t (MotionDfst m) -> [String]
dotSourceEdges makeLabel src dsts = DM.foldrWithKey
  (\lo hi motion xs -> dotEdge makeLabel src lo hi motion : xs) [] dsts

dotEdge :: (t -> t -> m -> String) -> Int -> t -> t -> MotionDfst m -> String
dotEdge makeLabel src lo hi (MotionDfst dst output) =
  "  N" ++ show src ++ " -> N" ++ show dst ++ " [label=\"" ++ escapeQuotes (makeLabel lo hi output) ++ "\"];\n"

escapeQuotes :: String -> String
escapeQuotes str = do
  c <- str
  case c of
    '"' -> "\\\""
    '\\' -> "\\\\"
    _ -> [c]

