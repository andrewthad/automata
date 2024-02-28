{-# language BangPatterns #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}

module Automata.Internal.Partition
  ( Partition
  , Partitions
  , newPartitions
  , finishPartitions
  , partitionStates
  , partitionCardinality
  , splitPartitions
  ) where

import Control.Monad.ST (ST,runST)
import Data.STRef (STRef,readSTRef,writeSTRef,newSTRef)
import Data.Primitive (PrimArray,MutablePrimArray,MutableArray)
import Data.Map (Map)
import Data.Set (Set)

import qualified Data.Set as S
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Set.Unboxed as SU
import qualified Data.Primitive as PM
import qualified Data.Primitive.Contiguous as C

data Partition s = Partition
  !Int -- identifier, these are produced from a monotonically increasing source
  !(STRef s (Metadata s))

instance Eq (Partition s) where
  Partition x _ == Partition y _ = x == y

instance Ord (Partition s) where
  compare (Partition x _) (Partition y _) = compare x y

instance Show (Partition s) where
  show (Partition x _) = show x

data Metadata s = Metadata
  !Int -- Current size of the partition
  !(MutablePrimArray s Int) -- Elements in the partition

-- A partitioning of contiguous machine integers
data Partitions s = Partitions
  !Int -- upper bound on values that can be inserted, used for error checking
  !(MutablePrimArray s Int) -- singleton array with next partition identifier
  !(STRef s [Partition s])
  -- All of the partitions. On the wikipedia page for partition refinement,
  -- it claims that this needs to support cheap insertion into the middle
  -- of the array. However, I do not believe this is true. It should be
  -- fine to always cons onto the front of the list.
  !(MutableArray s (Partition s)) -- Map from element to set identifier
  !(MutablePrimArray s Int)
  -- Map from element to index in partition. This is only meaningful
  -- when you already know the partition that the element is in.

ex1 :: ([Set Int],[Int])
ex1 = runST $ do
  (p,_) <- newPartitions 7
  xs1 <- splitPartitions p (SU.fromList [5,4,2])
  xs2 <- splitPartitions p (SU.fromList [4,2,0,1])
  xs3 <- splitPartitions p (SU.fromList [4,2,0])
  xs4 <- splitPartitions p (SU.fromList [2,6,0])
  xs5 <- splitPartitions p (SU.fromList [2,6,4])
  r <- finishPartitions p
  pure (r,[length xs1,length xs2,length xs3,length xs4,length xs5])

finishPartitions :: Partitions s -> ST s [Set Int]
finishPartitions (Partitions _ _ ps _ _) = do
  xs <- readSTRef ps
  F.foldlM
    (\ys (Partition _ r) -> do
      Metadata sz elements <- readSTRef r
      if sz > 0
        then do
          let go !ix !s = if ix >= 0
                then do
                  e <- PM.readPrimArray elements ix
                  go (ix - 1) (S.insert e s)
                else pure s
          y <- go (sz - 1) S.empty
          pure (y : ys)
        else pure ys
    ) [] xs

-- This starts out with just one big partition.
newPartitions :: Int -> ST s (Partitions s, Partition s)
newPartitions !total = do
  counter <- PM.newPrimArray 1
  PM.writePrimArray counter 0 (1 :: Int)
  let go !ix !arr = if ix >= 0
        then do
          PM.writePrimArray arr ix ix
          go (ix - 1) arr
        else pure ()
  allElements <- PM.newPrimArray total
  go (total - 1) allElements
  elementToIndex <- PM.newPrimArray total
  go (total - 1) elementToIndex
  meta0 <- newSTRef (Metadata total allElements)
  let p0 = Partition 0 meta0
  partitionList <- newSTRef [p0]
  elementToPartition <- PM.newArray total p0
  pure (Partitions total counter partitionList elementToPartition elementToIndex, p0)
  
-- In the returned tuples, the first element is the already-existing partition
-- (which may have shrunk) and the second element is the newly-created partition.
splitPartitions :: forall s. Partitions s -> SU.Set Int -> ST s [(Partition s,Partition s)]
splitPartitions (Partitions total counter partitionList elementToPartition elementToIndex) distinction = do
  c0 <- PM.readPrimArray counter 0
  partitionListA <- readSTRef partitionList
  (partitionListB, updatedPartitionPairs, c1) <- go c0 partitionListA [] M.empty (SU.toList distinction)
  PM.writePrimArray counter 0 c1
  writeSTRef partitionList partitionListB
  pure updatedPartitionPairs
  where
  -- Invariant: the keys of the recend partition map must match the
  -- partition identifiers in the values.
  go :: Int -> [Partition s] -> [(Partition s, Partition s)]
     -> Map Int (Partition s) -> [Int]
     -> ST s ([Partition s],[(Partition s, Partition s)],Int)
  go !cntr !plist !pnew !_ [] = pure (plist,pnew,cntr)
  go !cntr !plist !pnew !recent (x : xs) = if x >= total
    then error "Automata.Internal: tried to refine partition with unacceptably large value"
    else do
      poriginal@(Partition pnum mreforiginal) <- PM.readArray elementToPartition x
      -- Remove the element from the original partition. To do
      -- this, we must look up its position, move the last element
      -- in the partition into this position and then update the
      -- position of what was previously the last element. 
      Metadata origSz origElems <- readSTRef mreforiginal
      origLast <- PM.readPrimArray origElems (origSz - 1)
      origIx <- PM.readPrimArray elementToIndex x
      PM.writePrimArray origElems origIx origLast
      PM.writePrimArray elementToIndex origLast origIx
      writeSTRef mreforiginal $! Metadata (origSz - 1) origElems
      case M.lookup pnum recent of
        Nothing -> do
          pelems <- PM.newPrimArray 1
          PM.writePrimArray pelems 0 x
          let m = Metadata 1 pelems
          mref <- newSTRef m
          let !p = Partition cntr mref
          -- Add the element to the new partition. It was removed
          -- earlier before the case statement.
          PM.writeArray elementToPartition x p
          PM.writePrimArray elementToIndex x 0
          go (cntr + 1) (p : plist) ((poriginal,p) : pnew) (M.insert pnum p recent) xs
        Just myPartition@(Partition _ metaref) -> do
          Metadata sz buf <- readSTRef metaref
          bufSz <- PM.getSizeofMutablePrimArray buf
          PM.writeArray elementToPartition x myPartition
          PM.writePrimArray elementToIndex x sz
          if sz < bufSz
            then do
              PM.writePrimArray buf sz x
              writeSTRef metaref $! Metadata (sz + 1) buf
            else do
              let newBufSz = bufSz * 2
              newBuf <- PM.newPrimArray newBufSz
              PM.setPrimArray newBuf 0 newBufSz 12345678
              PM.copyMutablePrimArray newBuf 0 buf 0 bufSz
              -- intentionally using the old size as the index
              PM.writePrimArray newBuf sz x
              writeSTRef metaref $! Metadata (sz + 1) newBuf
          go cntr plist pnew recent xs

partitionCardinality :: Partition s -> ST s Int
partitionCardinality (Partition _ r) = do
  Metadata card _ <- readSTRef r
  pure card

partitionStates :: Partition s -> ST s (PrimArray Int)
partitionStates (Partition _ r) = do
  Metadata card arr <- readSTRef r
  C.freeze (C.sliceMut arr 0 card)
