{-# LANGUAGE BangPatterns #-}
{- OPTIONS_GHC -ddump-simpl #-}
module PTree (
    Chunk (..)
  , PTreeST
  , PTree
  , freezePTree
  , newPTreeST
  , modifyPTreeST
  , pTreeSTtoChunks
  ) where
import Control.Monad.ST (ST)
import Data.STRef

data Chunk seg = Equal !seg | Between !seg

data PTreeST s seg a
  = NodeST !(PTreeST s seg a) !a !(STRef s seg) !(PTreeST s seg a)
  | LeafST !(STRef s seg)

data PTree seg a
  = Node !(PTree seg a) !a !seg !(PTree seg a)
  | Leaf !seg
  deriving (Show)

pTreeSTtoChunks :: PTreeST s seg a -> ST s [Chunk seg]
pTreeSTtoChunks t = pTreeToChunks <$> freezePTree t

pTreeToChunks :: PTree seg a -> [Chunk seg]
pTreeToChunks = flip go []
  where
    go (Leaf seg) rest = Between seg : rest
    go (Node left _k seg right) rest =
      go left $ Equal seg : go right rest

freezePTree :: PTreeST s seg a -> ST s (PTree seg a)
freezePTree (LeafST ref) = Leaf <$> readSTRef ref
freezePTree (NodeST l a mid r) = Node <$> freezePTree l <*> pure a <*> readSTRef mid <*> freezePTree r

modifyPTreeST :: Ord a => PTreeST s seg a -> a -> (seg -> a -> seg) -> ST s ()
modifyPTreeST t0 a0 f = go t0 a0
  where
    go (LeafST ref) a = modifySTRef' ref (\seg -> f seg a)
    go (NodeST left rk rv right) a =
      case compare a rk of
        LT -> go left a
        GT -> go right a
        EQ -> modifySTRef' rv (\seg -> f seg a)

newPTreeST :: seg -> [a] -> ST s (PTreeST s seg a)
newPTreeST seg xs = do
  (pt, remains) <- newPTreeST' seg (length xs) xs
  if null remains
    then
      pure pt
    else
      error "Unexpected remains"

newPTreeST' :: seg -> Int -> [a] -> ST s (PTreeST s seg a, [a])
newPTreeST' !seg 0 as = do
  r <- newSTRef seg
  pure (LeafST r, as)
newPTreeST' !seg !n !as = case n `quot` 2 of
  qt ->
    do
      (l, rest) <- newPTreeST' seg qt as
      (a, as') <- case rest of
        a : as'-> pure (a, as')
        _ -> error "List too short"
      md <- newSTRef seg
      (r, as'') <- newPTreeST' seg (n - qt - 1) as'
      pure (NodeST l a md r, as'')

{-
--For debugging

-- Check whether a PTree is balanced. In particular, ensure that the numbers of
-- leaves in the left and right children of each node differ by at most one.
balanced :: PTree seg a -> Bool
balanced = fst . balanced'

balanced' :: PTree seg a -> (Bool, Int)
balanced' (Leaf {}) = (True, 1)
balanced' (Node l _ _ r)
  | (lb, lc) <- balanced' l
  , (rb, rc) <- balanced' r
  , !bal <- lb && rb && abs (lc - rc) <= 1
  , !c <- lc + rc
  = (bal, c)
  -}
