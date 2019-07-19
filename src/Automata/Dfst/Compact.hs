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

import Automata.Internal.Transducer (MotionCompactDfst(..))
import Automata.Internal.Transducer (CompactDfst(..),Dfst(..),MotionDfst(..),CompactSequence(..),TransitionCompactDfst(..))
import Control.Monad.ST (runST)
import Control.Monad (forM_)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe,isJust)
import Data.Primitive (Array,sizeofArray)
import Data.Semigroup (Last(..))
import Data.Bool (bool)
import Data.Monoid (Sum(..))
import Data.Foldable (foldlM)
import Control.Monad.Trans.State.Strict (get,put,runState)

import qualified Data.Foldable as F
import qualified Data.DisjointMap as DJM
import qualified Data.List as L
import qualified Data.Map.Interval.DBTSLL as DM
import qualified Data.Map.Strict as M
import qualified Data.Primitive as P
import qualified Data.Primitive as PM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set.Lifted as SL
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
states (CompactDfst t _ _) = P.sizeofArray t

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

compact :: forall t m. (Ord m, Enum t, Ord t, Bounded t)
  => Dfst t m
  -> CompactDfst t m
compact (Dfst transitions finals) =
  let outputs = SL.fromList $ F.foldr (\m xs -> F.foldr (\(MotionDfst _ out) ys -> out : ys) xs m) [] transitions
      outputToIndex out = fromMaybe
        (error ("Automata.Dfst.Compact.compact: bad output token, sz=" ++ show (F.length outputs) ++ ",trans_lens=" ++ show (fmap F.length transitions)))
        (SL.lookupIndex out outputs)
      -- How many transitions there are from other nodes to each node.
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
          -- TODO: remember why this is commented out.
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
          (\(oldToNew',newToOld') old -> if old == 0 || isJust (M.lookup old (fst m1))
            then pure (oldToNew',newToOld')
            else do
              new <- get
              put (new + 1)
              pure (M.insert old new oldToNew', M.insert new old newToOld')
          ) m1 (enumFromTo 0 (PM.sizeofArray transitions - 1))
      newTransitions = runST $ do
        theStates <- C.new totalStates
        forM_ (enumFromTo 0 (totalStates - 1)) $ \ix -> do
          let ixOld = newToOld M.! ix
          case DJM.lookup' ixOld collapseFinal of
            Nothing -> do
              PM.writeArray theStates ix $ TransitionCompactDfstMultiple
                $ DM.map (\(MotionDfst s out) -> MotionCompactDfst (oldToNew M.! s) (outputToIndex out))
                $ PM.indexArray transitions ixOld
            Just ([], _) -> error "Automata.Dfst.Compact.compact: empty string"
            Just (string@(_ : _), Last successStateOld) -> do
              PM.writeArray theStates ix $ TransitionCompactDfstSingle $ CompactSequence
                (E.fromList string)
                (oldToNew M.! successStateOld)
                (oldToNew M.! (motionDfstState (snd (singles M.! ixOld))))
                (outputToIndex (motionDfstOutput (fst (singles M.! ixOld))))
                (outputToIndex (motionDfstOutput (snd (singles M.! ixOld))))
        PM.unsafeFreezeArray theStates
      newFinals = SU.fromList (L.map (fromMaybe (error "Automata.Dfst.Compact.compact") . flip M.lookup oldToNew) (SU.toList finals))
   in CompactDfst newTransitions newFinals (SL.toArray outputs)

evaluateList :: forall t m. Ord t
  => CompactDfst t m
  -> [t]
  -> Maybe (Array (Ranged m))
evaluateList (CompactDfst transitions finals outputs) tokensX = case tokensX of
  [] -> bool Nothing (Just mempty) (SU.member 0 finals)
  token0 : tokens0 -> case PM.indexArray transitions 0 of
    TransitionCompactDfstSingle (CompactSequence string successState failureState successToken failureToken) ->
      if PM.indexArray string 0 == token0
        -- Sequences are guaranteed to have length >= 1, so this indexing does
        -- not need to be guarded.
        then goSequence string 1 (PM.sizeofArray string) successState failureState failureToken 1 0 successToken 0 [] tokens0
        else goUnknown failureState 1 0 failureToken 0 [] tokens0
    TransitionCompactDfstMultiple theMap ->
      let MotionCompactDfst nextState outputTokenIndex = DM.lookup token0 theMap
       in goUnknown nextState 1 0 outputTokenIndex 0 [] tokens0
  where
  goSequence :: Array t -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> [Ranged m] -> [t] -> Maybe (Array (Ranged m))
  goSequence !string !stringIx !stringSz !successState !failureState !failureTokenIndex !ix !outputSz !nextOutputTokenIndex !nextOutputStart !output !tokensA = case tokensA of
    [] -> if stringIx < stringSz
      -- Sequences may not contain final states, so mid-sequence input
      -- termination always indicates an unrecognized input.
      then Nothing
      else if SU.member successState finals
        then let !r' = r in Just $! C.unsafeFromListReverseN (outputSz + 1) (r' : output)
        else Nothing
    tokenB : tokensB -> if stringIx < stringSz
      then if PM.indexArray string stringIx == tokenB
        then goSequence string (stringIx + 1) stringSz successState failureState failureTokenIndex (ix + 1) outputSz nextOutputTokenIndex nextOutputStart output tokensB
        else bool
          (let !r' = r in goUnknown failureState (ix + 1) (outputSz + 1) failureTokenIndex ix (r' : output) tokensB)
          (goUnknown failureState (ix + 1) outputSz failureTokenIndex nextOutputStart output tokensB)
          (nextOutputTokenIndex == failureTokenIndex)
      else goUnknown successState ix outputSz nextOutputTokenIndex nextOutputStart output (tokenB : tokensB)
    where
    {-# INLINE r #-}
    r = Ranged nextOutputStart (ix - nextOutputStart) (PM.indexArray outputs nextOutputTokenIndex)
  goUnknown :: Int -> Int -> Int -> Int -> Int -> [Ranged m] -> [t] -> Maybe (Array (Ranged m))
  goUnknown !state !ix !outputSz !nextOutputTokenIndex !nextOutputStart !output !tokensA = case tokensA of
    [] -> if SU.member state finals
      then let !r' = r in Just $! C.unsafeFromListReverseN (outputSz + 1) (r' : output)
      else Nothing
    tokenB : tokensB -> case PM.indexArray transitions state of
      TransitionCompactDfstSingle (CompactSequence string successState failureState successTokenIndex failureTokenIndex) ->
        if PM.indexArray string 0 == tokenB
          -- Sequences are guaranteed to have length >= 1, so this indexing does
          -- not need to be guarded.
          then bool
            (let !r' = r in goSequence string 1 (PM.sizeofArray string) successState failureState failureTokenIndex (ix + 1) (outputSz + 1) successTokenIndex ix (r' : output) tokensB)
            (goSequence string 1 (PM.sizeofArray string) successState failureState failureTokenIndex (ix + 1) outputSz successTokenIndex nextOutputStart output tokensB)
            (nextOutputTokenIndex == successTokenIndex)
          else bool
            (let !r' = r in goUnknown failureState (ix + 1) (outputSz + 1) failureTokenIndex ix (r' : output) tokensB)
            (goUnknown failureState (ix + 1) outputSz failureTokenIndex nextOutputStart output tokensB)
            (nextOutputTokenIndex == failureTokenIndex)
      TransitionCompactDfstMultiple theMap ->
        let MotionCompactDfst nextState outputIndex = DM.lookup tokenB theMap
         in bool
              (let !r' = r in goUnknown nextState (ix + 1) (outputSz + 1) outputIndex ix (r' : output) tokensB)
              (goUnknown nextState (ix + 1) outputSz outputIndex nextOutputStart output tokensB)
              (nextOutputTokenIndex == outputIndex)
    where
    {-# INLINE r #-}
    r = Ranged nextOutputStart (ix - nextOutputStart) (PM.indexArray outputs nextOutputTokenIndex)


toDot :: (Bounded t, Enum t)
  => ([t] -> m -> String) -- ^ Label a sequence
  -> (t -> t -> m -> String) -- ^ Label a range
  -> CompactDfst t m
  -> String
toDot makeSequenceLabel makeLabel (CompactDfst ts fs outputs) = concat $
  [ "digraph D {\n" ]
  ++
  dotNodes (sizeofArray ts - 1) fs
  ++
  (do (src,m) <- zip (enumFrom (0 :: Int)) (E.toList ts)
      case m of
        TransitionCompactDfstMultiple motions ->
          dotSourceEdges makeLabel outputs src motions
        TransitionCompactDfstSingle (CompactSequence inputs successState failureState successOutput failureOutput) ->
          [ "  N" ++ show src ++ " -> N" ++ show successState ++ " [label=\"" ++ escapeQuotes (makeSequenceLabel (E.toList inputs) (PM.indexArray outputs successOutput)) ++ "\"];\n"
          , "  N" ++ show src ++ " -> N" ++ show failureState ++ " [label=\"" ++ escapeQuotes (makeSequenceLabel [] (PM.indexArray outputs failureOutput)) ++ "\"];\n"
          ]
  )
  ++
  [ "}\n" ]

dotNodes :: Int -> SU.Set Int -> [String]
dotNodes n fs = if n >= 0
  then ("  N" ++ show n ++ " [shape=" ++ (if SU.member n fs then "circle" else "square") ++ "];\n") : dotNodes (n - 1) fs
  else []

dotSourceEdges :: (Bounded t, Enum t)
  => (t -> t -> m -> String) -> Array m -> Int
  -> DM.Map t MotionCompactDfst -> [String]
dotSourceEdges makeLabel outputs src dsts = DM.foldrWithKey
  (\lo hi motion xs -> dotEdge makeLabel outputs src lo hi motion : xs) [] dsts

dotEdge :: (t -> t -> m -> String) -> Array m -> Int -> t -> t -> MotionCompactDfst -> String
dotEdge makeLabel outputs src lo hi (MotionCompactDfst dst output) =
  "  N" ++ show src ++ " -> N" ++ show dst ++ " [label=\"" ++ escapeQuotes (makeLabel lo hi (PM.indexArray outputs output)) ++ "\"];\n"

escapeQuotes :: String -> String
escapeQuotes str = do
  c <- str
  case c of
    '"' -> "\\\""
    '\\' -> "\\\\"
    _ -> [c]

