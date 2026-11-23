{-# language BangPatterns #-}
{-# language DeriveFunctor #-}
{-# language ScopedTypeVariables #-}
{-# language UnboxedTuples #-}
{-# language EmptyCase #-}

-- for debugging
{-# language StandaloneDeriving #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{- OPTIONS_GHC -ddump-simpl #-}
module Sample where

import Data.Sequence.Internal
  ( Seq (..)
  , FingerTree (..)
  , Node (..)
  , Digit (..)
  , Sized (..)
  , Elem (..)
  )
import qualified Data.Sequence as S
import System.Random
import Data.Sequence ((|>), index, splitAt, empty)
import Prelude hiding (splitAt)
--import Debug.Trace
import Control.Exception (assert)
import qualified Data.List as L
import qualified Data.Foldable as F
import PTree
import Control.Monad.ST (runST)
import Data.Foldable (forM_)
import Data.Maybe (mapMaybe)
--import GHC.Exts (noinline)

-- A tree of sequences annotated by total length. The elements of each sequence are
-- less than or equal to those of following sequences.
--
-- TODO: Currently, once we know that a subsequence is sorted, we break it up into a
-- bunch of singletons. Another option might be to tag the sequences in the Parted
-- to indicate whether they're known to be sorted. This might help limit long-lived
-- clutter at the expense of more (hopefully short term) clutter. It might be beneficial
-- to combine division-by-sorting for small pieces with eager construction of small
-- nodes, to clear most of the little clutter bits quickly.
data Segment a = Unsorted !(Seq a) | Sorted !(Seq a)
type Parted a = FingerTree (Segment a)

instance Sized (Seq a) where
  size = length

instance Sized (Segment a) where
  size (Unsorted x) = length x
  size (Sorted x) = length x

instance Sized a => Sized (Chunk a) where
  size (Equal xs) = size xs
  size (Between xs) = size xs

splatterSeq :: forall a. Ord a => [a] -> Seq a -> Parted a
splatterSeq pivots s = runST $ do
  t <- newPTreeST empty pivots
  forM_ s $ \a -> modifyPTreeST t a (|>)
  raw_chunks <- pTreeSTtoChunks t
  pure $ foldl' snocTree EmptyT $ mapMaybe check raw_chunks
  where
    check (Equal x) = Just $ Sorted x -- The pivot comes from the list, so it will always be found there
    check (Between x)
      | null x = Nothing
      | otherwise = Just $ Unsorted x

-- Partition a sequence around a particular value, maintaining the ordering of
-- equal values.
partitionSeq :: forall a. Ord a => a -> Seq a -> StrictTriple (Seq a) (Seq a) (Seq a)
partitionSeq pivot = foldl' go (TripleS S.empty S.empty S.empty)
  where
    go (TripleS less same more) a = case compare a pivot of
      LT -> TripleS (less |> a) same more
      EQ -> TripleS less (same |> a) more
      GT -> TripleS less same (more |> a)

{-
partitionSeq !pivot (Seq t) =
  case partitionFT go t S.empty S.empty S.empty of
    (# less, same, more #) -> TripleS less same more
  where
    go :: Elem a -> Seq a -> Seq a -> Seq a -> (# Seq a, Seq a, Seq a #)
    go (Elem !a) less same more = case compare a pivot of
      LT -> let !less' = less |> a in (# less', same, more #)
      EQ -> let !same' = same |> a in (# less, same', more #)
      GT -> let !more' = more |> a in (# less, same, more' #)
partitionFT :: (n -> sa -> sa -> sa -> (# sa, sa, sa #)) -> FingerTree n -> sa -> sa -> sa -> (# sa, sa, sa #)
partitionFT _f EmptyT !less !same !more = (# less, same, more #)
partitionFT f (Single n) !less !same !more = f n less same more
partitionFT f (Deep _s pr m sf) !less !same !more =
  case partitionDigit f pr less same more of { (# less', same', more' #) -> 
  case partitionFT f' m less' same' more' of { (# less'', same'', more'' #) ->
    partitionDigit f sf less'' same'' more'' }}
  where
--    f' :: Node n -> sa -> sa -> sa -> (# sa, sa, sa #)
    f' (Node2 _s n1 n2) l s mo =
      case f n1 l s mo of
        (# l', s', mo' #) -> f n2 l' s' mo'
    f' (Node3 _s n1 n2 n3) l s mo =
      case f n1 l s mo of { (# l', s', mo' #) ->
      case f n2 l' s' mo' of
        (# l'', s'', mo'' #) -> f n3 l'' s'' mo'' }


partitionDigit :: (n -> sa -> sa -> sa -> (# sa, sa, sa #)) -> Digit n -> sa -> sa -> sa -> (# sa, sa, sa #)
partitionDigit f (One a) less same more = f a less same more
partitionDigit f (Two a b) less same more =
  case f a less same more of { (# less', same', more' #) ->
    f b less' same' more' }
partitionDigit f (Three a b c) less same more =
  case f a less same more of { (# less', same', more' #) ->
  case f b less' same' more' of { (# less'', same'', more'' #) ->
    f c less'' same'' more''
  }}
partitionDigit f (Four a b c d) less same more =
  case f a less same more of { (# less', same', more' #) ->
  case f b less' same' more' of { (# less'', same'', more'' #) ->
  case f c less'' same'' more'' of { (# less''', same''', more''' #) ->
    f d less''' same''' more'''
  }}}
  -}

incSort :: Ord a => StdGen -> Seq a -> Seq a
incSort !_g (Seq EmptyT) = S.empty
incSort !_g s@(Seq (Single !_)) = s
incSort g s = Seq $ doSort (length s) 1 des_elem unpackSingleton g (Single (Unsorted s))
  where
    unpackSingleton _g (Single (Sorted (Seq (Single x)))) = x
    unpackSingleton _g (Single (Unsorted (Seq (Single x)))) = x
    unpackSingleton _ _ = error "Parted is not a singleton at the leaf"
    
    des_elem [] = error "Can't get blood from a stone."
    des_elem (x : xs) = (Elem x, xs)

doSort :: forall a b. Ord a => Int -> Int -> ([a] -> (b, [a])) -> (StdGen -> Parted a -> b) -> StdGen -> Parted a -> FingerTree b
-- This is awful. It would be nicer to use some sort of appropriate functor, I imagine.
doSort n !mSize des m = case n of
    0 -> emptyTree
    1 -> \ !g !p -> Single (m g p)
    2 -> deepA 1 one emptyTree 1 one
    3 -> deepA 2 two emptyTree 1 one
    4 -> deepA 2 two emptyTree 2 two
    5 -> deepA 3 three emptyTree 2 two
    6 -> deepA 3 three emptyTree 3 three
    _ -> case n `quotRem` 3 of
           (q,0) -> deepA 3 three (doSort (q - 2) mSize' des3 n3) 3 three
           (q,1) -> deepA 2 two (doSort (q - 1) mSize' des3 n3) 2 two
           (q,_) -> deepA 3 three (doSort (q - 1) mSize' des3 n3) 2 two
      where !mSize' = 3 * mSize
            des3 :: [a] -> (Node b, [a])
            des3 xs
              | (!t1, xs') <- des xs
              , (!t2, xs'') <- des xs'
              , (!t3, xs''') <- des xs''
              = (Node3 mSize' t1 t2 t3, xs''')

            n3 g p
              | mSize' <= 81*3 =
                  case des3 (concatSegments p) of
                    (nd, remains) -> assert (F.null remains) nd
              | otherwise = Node3 mSize' lres mres rres
              where
                concatSegments :: Parted a -> [a]
                concatSegments ss =
                  [a | seg <- F.toList ss
                     , let s = case seg of
                                 Sorted q -> q
                                 Unsorted q -> S.sort q
                     , a <- F.toList s]
                (lres, mres, rres) =
                  case divideParted g mSize p of { TripleS left rest g' ->
                  case divideParted g' mSize rest of { TripleS mid right g'' ->
                  case splitGen g'' of { (g1, g''') ->
                  case splitGen g''' of { (g2, g3) ->
                     (m g1 left, m g2 mid, m g3 right) }}}}
  where
    deepA :: Int -> (StdGen -> Parted a -> Digit b) -> (StdGen -> Parted a -> FingerTree (Node b)) -> Int -> (StdGen -> Parted a -> Digit b) -> StdGen -> Parted a -> FingerTree b
    deepA prl prg mg sfl sfg g p =
      case divideParted g (prl * mSize) p of { TripleS left rest g' ->
      case divideParted g' (mSize * (n - prl - sfl)) rest of { TripleS mid right g'' ->
      case splitGen g'' of { (g1, g''') ->
      case splitGen g''' of { (g2, g3) ->
        Deep (n * mSize) (prg g1 left) (mg g2 mid) (sfg g3 right)
        }}}}

    one :: StdGen -> Parted a -> Digit b
    one !g !p = One (m g p)

    two :: StdGen -> Parted a -> Digit b
    two !g !p = Two lres rres
      where
        (lres, rres) =
          case divideParted g mSize p of { (TripleS p1 p2 g') ->
          case splitGen g' of { (g1, g2) ->
            (m g1 p1, m g2 p2) }}

    three :: StdGen -> Parted a -> Digit b
    three !g !p = Three lres mres rres
      where
        (lres, mres, rres) =
          case divideParted g mSize p of { TripleS p1 p' g' ->
          case divideParted g' mSize p' of { TripleS p2 p3 g'' ->
          case splitGen g'' of { (g1, g''') ->
          case splitGen g''' of { (g2, g3) ->
            (m g1 p1, m g2 p2, m g3 p3) }}}}

    emptyTree !_g !_p = EmptyT


-- TODO: choose sample size cutoffs much more carefully. I suspect we'll want
-- to go up to 7-element samples at some size, and *possibly* even larger ones.
-- My intuition: the larger the sequence, the more expensive it is to choose a
-- "bad" pivot.
choosePivot :: Ord a => StdGen -> Seq a -> StrictPair a StdGen
choosePivot g s
  | length s < 100
  = case uniformR (0, length s - 1) g
      of
        (i, g') -> (s `index` i) :*: g'
  | length s < 1000
  = case uniformListR 5 (0, length s - 1) g
      of
        (candindices, g') -> (L.sort (fmap (s `index`) candindices) !! 2) :*: g'
  | otherwise
  = case uniformListR 7 (0, length s - 1) g
      of
        (candindices, g') -> (L.sort (fmap (s `index`) candindices) !! 3) :*: g'

choosePivots :: Ord a => StdGen -> Seq a -> StrictPair [a] StdGen
choosePivots g s
  | (sample_ixs, g') <- uniformListR (desired_pivots * 2 + 1) (0, length s - 1) g
  , let raw_sample = [s `index` i | i <- sample_ixs]
        clean_sample = mergeEquals (L.sort raw_sample)
  = skipping 1 clean_sample :*: g'
  where
    -- The number of pivots we attempt to choos. We may not get this number if
    -- too many elements in the sample are equal. We always want one less than
    -- a power of two, to make the binary tree most effective, but we deal with
    -- whatever we get.
    desired_pivots :: Int
    desired_pivots
      | length s < 3000 = 3
      | otherwise = 7
--    _ t _ t _ t _         k * 2 + 1
--    _ _ t _ _ t _ _ t _ _   k * 3 + 2
--    _ _ _ t _ _ _ t _ _ _ t _ _ _    k + 3 * (k + 1)    =   4 * k + 3
--      k + 4 * (k + 1)
--      k + j * (k + 1)   =   k + j*k + j    =   k (1 + j) + j

skipping :: Int -> [a] -> [a]
skipping n xs =
  case L.drop n xs of
    [] -> []
    a : as -> a : skipping n as

-- Discard repeats from a sorted list
mergeEquals :: Eq a => [a] -> [a]
mergeEquals [] = []
mergeEquals (a : as) = a : go a as
  where
    go !_x [] = []
    go x (y : zs)
      | x == y = go x zs
      | otherwise = y : go y zs


infixr 5 <<|
infixl 5 |>>
{-# NOINLINE (<<|) #-}
(<<|) :: Segment a -> Parted a -> Parted a
s <<| p
  | size s == 0 = p
  | otherwise = s `consTree` p

{-# NOINLINE (|>>) #-}
(|>>) :: Parted a -> Segment a -> Parted a
p |>> s
  | size s == 0 = p
  | otherwise = p `snocTree` s


divideParted :: Ord a => StdGen -> Int -> Parted a -> StrictTriple (Parted a) (Parted a) StdGen
divideParted g i p = divideParted1 g i EmptyT p EmptyT
{-
divideParted g !_i EmptyT = TripleS EmptyT EmptyT g
divideParted g i p = assert (i >= 0) $
  case splitTreeN i p of
    Split before during after ->
      let
        i' = i - size before
        res = divideParted' g i' before during after
        good (TripleS l r _) = size l == i && i + size r == size p
      in assert (good res) res
-}

divideParted1 :: Ord a => StdGen -> Int -> Parted a -> Parted a -> Parted a -> StrictTriple (Parted a) (Parted a) StdGen
divideParted1 g !_i before EmptyT after = TripleS before after g
divideParted1 g i before' p after' = assert (i >= 0) $
  case splitTreeN i p of
    Split before during after ->
      let
        i' = i - size before
        res = divideParted' g i' (before' `appendTree0` before) during (after `appendTree` after')
        -- good (TripleS l r _) = size l == i && i + size r == size p
      in {- assert (good res) -} res

instance (Show a, b ~ Seq a) => Show (FingerTree b) where
  -- This mapping is completely illegitimate, but it's okay because the Show instance
  -- doesn't care about size annotations.
  showsPrec i t = showsPrec i (Seq (fmap Elem t))


divideParted' :: Ord a => StdGen -> Int -> Parted a -> Segment a -> Parted a -> StrictTriple (Parted a) (Parted a) StdGen
divideParted' g i before (Sorted s) after =
  case splitAt i s of
    (less, more) -> TripleS (before |>> Sorted less) (Sorted more <<| after) g
divideParted' g i before (Unsorted during) after
  | length during < 81
  = divideParted' g i before (Sorted (S.sort during)) after
divideParted' g i before (Unsorted during) after =
  case choosePivots g during of
    pivots :*: g' ->
      case splitTreeN i splattered of
        Split less same more
          | i < length less
          -> _ -- divideParted' g' i before

          -- TripleS (before `appendTree0` l) undefined undefined
      where
        splattered = splatterSeq pivots during


{-
divideParted' g i before (Unsorted during) after =
  case choosePivot g during of
    pivot :*: g' -> case partitionSeq pivot during of
      TripleS less same more
        | i < length less
        -> divideParted' g' i before (Unsorted less) (Sorted same `consTree` Unsorted more <<| after)
        | let i' = i - length less
        , i' < length same
        -> case splitAt i' same of
             (boo, yah) -> TripleS (before |>> Unsorted less |>> Sorted boo) (Sorted yah <<| Unsorted more <<| after) g'
        | let i' = i - length less - length same
        -> divideParted' g' i' (before |>> Unsorted less `snocTree` Sorted same) (Unsorted more) after
        -}


{-
divideParted' g i before during@(Seq (Single _)) after
  | i == 0 = TripleS before (during `consTree` after) g
  | otherwise = TripleS (before `snocTree` during) after g
        -}


-- CAUTION: Split should only be used for *data* like Node or Seq, not for
-- Elem. Otherwise, it will force things illegitimately.
data Split a = Split !(FingerTree a) !a !(FingerTree a)
data StrictPair a b = !a :*: !b
  deriving (Show)

infixr 1 :*:

deriving instance (Show a, b ~ Seq a) => Show (Split b)

data StrictTriple a b c = TripleS !a !b !c
  deriving (Show)

forceSpineTree :: FingerTree a -> ()
forceSpineTree (Deep _n _pr m _sf) = forceSpineTree m
forceSpineTree _ = ()

forceSpine :: Seq a -> ()
forceSpine (Seq t) = forceSpineTree t

class Valid a where
    valid :: a -> Bool
       
instance Valid (Elem a) where
    valid _ = True
       
instance Valid (Seq a) where
    valid (Seq xs) = valid xs
       
instance (Sized a, Valid a) => Valid (FingerTree a) where
    valid EmptyT = True
    valid (Single x) = valid x
    valid (Deep s pr m sf) =
        s == size pr + size m + size sf && valid pr && valid m && valid sf
       
instance (Sized a, Valid a) => Valid (Node a) where
    valid node = size node == sum (fmap size node) && all valid node
       
instance Valid a => Valid (Digit a) where
    valid = all valid 



-- WARNING: This function forces the item being split around. Normally, it should
-- not be used to split around an Elem.
{-# SPECIALIZE splitTreeN :: Int -> FingerTree (Node a) -> Split (Node a) #-}
{-# SPECIALIZE splitTreeN :: Int -> FingerTree (Segment a) -> Split (Segment a) #-}
splitTreeN :: Sized a => Int -> FingerTree a -> Split a
splitTreeN !_i EmptyT = error "splitTreeN of empty tree"
splitTreeN _i (Single x) = Split EmptyT x EmptyT
splitTreeN i (Deep s pr m sf)
  | i < spr     = splitPrefixN i s pr m sf
  | i < spm     = case splitTreeN im m of
            Split ml xs mr -> splitMiddleN (im - size ml) s spr pr ml xs mr sf
  | otherwise   = splitSuffixN (i - spm) s pr m sf  where
    spr     = size pr
    spm     = spr + size m
    im      = i - spr

{-# SPECIALIZE
   splitMiddleN ::  Int -> Int -> Int
             -> Digit (Node a) -> FingerTree (Node (Node a)) -> Node (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a)
             -> Split (Node a) #-}
splitMiddleN :: Sized a => Int -> Int -> Int
             -> Digit a -> FingerTree (Node a) -> Node a -> FingerTree (Node a) -> Digit a
             -> Split a
splitMiddleN i s spr pr ml (Node2 _ a b) mr sf
  | i < sa      = Split (pullR sprml pr ml) a (Deep (s - sprmla) (One b) mr sf)
  | otherwise   = Split (Deep sprmla pr ml (One a)) b (pullL (s - sprmla - size b) mr sf)
  where
    sa      = size a
    sprml   = spr + size ml
    sprmla  = sa + sprml
splitMiddleN i s spr pr ml (Node3 _ a b c) mr sf
  | i < sa      = Split (pullR sprml pr ml) a (Deep (s - sprmla) (Two b c) mr sf)
  | i < sab     = Split (Deep sprmla pr ml (One a)) b (Deep (s - sprmlab) (One c) mr sf)
  | otherwise   = Split (Deep sprmlab pr ml (Two a b)) c (pullL (s - sprmlab - size c) mr sf)
  where
    sa      = size a
    sab     = sa + size b
    sprml   = spr + size ml
    sprmla  = sa + sprml
    sprmlab = sprmla + size b

{-# SPECIALIZE
  splitPrefixN :: Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a) ->
     Split (Node a) #-}
splitPrefixN :: Sized a =>  Int -> Int -> Digit a -> FingerTree (Node a) -> Digit a ->
                    Split a
splitPrefixN !_i !s (One a) m sf = Split EmptyT a (pullL (s - size a) m sf)
splitPrefixN i s (Two a b) m sf
  | i < sa      = Split EmptyT a (Deep (s - sa) (One b) m sf)
  | otherwise   = Split (Single a) b (pullL (s - sa - size b) m sf)
  where
    sa      = size a
splitPrefixN i s (Three a b c) m sf
  | i < sa      = Split EmptyT a (Deep (s - sa) (Two b c) m sf)
  | i < sab     = Split (Single a) b (Deep (s - sab) (One c) m sf)
  | otherwise   = Split (Deep sab (One a) EmptyT (One b)) c (pullL (s - sab - size c) m sf)
  where
    sa      = size a
    sab     = sa + size b
splitPrefixN i s (Four a b c d) m sf
  | i < sa      = Split EmptyT a $ Deep (s - sa) (Three b c d) m sf
  | i < sab     = Split (Single a) b $ Deep (s - sab) (Two c d) m sf
  | i < sabc    = Split (Deep sab (One a) EmptyT (One b)) c $ Deep (s - sabc) (One d) m sf
  | otherwise   = Split (Deep sabc (Two a b) EmptyT (One c)) d $ pullL (s - sabc - size d) m sf
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c

{-# SPECIALIZE
  splitSuffixN :: Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a) ->
     Split (Node a) #-}
splitSuffixN :: Sized a => Int -> Int -> Digit a -> FingerTree (Node a) -> Digit a ->
   Split a
splitSuffixN !_i !s pr m (One a) = Split (pullR (s - size a) pr m) a EmptyT
splitSuffixN i s pr m (Two a b)
  | i < sa      = Split (pullR (s - sa - size b) pr m) a (Single b)
  | otherwise   = Split (Deep (s - size b) pr m (One a)) b EmptyT
  where
    sa      = size a
splitSuffixN i s pr m (Three a b c)
  | i < sa      = Split (pullR (s - sab - size c) pr m) a (deep (One b) EmptyT (One c))
  | i < sab     = Split (Deep (s - size b - size c) pr m (One a)) b (Single c)
  | otherwise   = Split (Deep (s - size c) pr m (Two a b)) c EmptyT
  where
    sa      = size a
    sab     = sa + size b
splitSuffixN i s pr m (Four a b c d)
  | i < sa      = Split (pullR (s - sa - sbcd) pr m) a (Deep sbcd (Two b c) EmptyT (One d))
  | i < sab     = Split (Deep (s - sbcd) pr m (One a)) b (Deep scd (One c) EmptyT (One d))
  | i < sabc    = Split (Deep (s - scd) pr m (Two a b)) c (Single d)
  | otherwise   = Split (Deep (s - sd) pr m (Three a b c)) d EmptyT
  where
    sa      = size a
    sab     = sa + size b
    sabc    = sab + size c
    sd      = size d
    scd     = size c + sd
    sbcd    = size b + scd




nodeToDigit :: Node a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

-- | Given the size of a digit and the digit itself, efficiently converts
-- it to a FingerTree.
digitToTree' :: Int -> Digit a -> FingerTree a
digitToTree' n (Four a b c d) = Deep n (Two a b) EmptyT (Two c d)
digitToTree' n (Three a b c) = Deep n (Two a b) EmptyT (One c)
digitToTree' n (Two a b) = Deep n (One a) EmptyT (One b)
digitToTree' !_n (One a) = Single a

{-# INLINE pullL #-}
pullL :: Int -> FingerTree (Node a) -> Digit a -> FingerTree a
pullL s m sf = case viewLTree m of
    EmptyLTree          -> digitToTree' s sf
    ConsLTree pr m'     -> Deep s (nodeToDigit pr) m' sf

{-# INLINE pullR #-}
pullR :: Int -> Digit a -> FingerTree (Node a) -> FingerTree a
pullR s pr m = case viewRTree m of
    EmptyRTree          -> digitToTree' s pr
    SnocRTree m' sf     -> Deep s pr m' (nodeToDigit sf)

data ViewLTree a = ConsLTree a (FingerTree a) | EmptyLTree
data ViewRTree a = SnocRTree (FingerTree a) a | EmptyRTree

{-# SPECIALIZE viewLTree :: FingerTree (Elem a) -> ViewLTree (Elem a) #-}
{-# SPECIALIZE viewLTree :: FingerTree (Node a) -> ViewLTree (Node a) #-}
viewLTree       :: Sized a => FingerTree a -> ViewLTree a
viewLTree EmptyT                = EmptyLTree
viewLTree (Single a)            = ConsLTree a EmptyT
viewLTree (Deep s (One a) m sf) = ConsLTree a (pullL (s - size a) m sf)
viewLTree (Deep s (Two a b) m sf) =
    ConsLTree a (Deep (s - size a) (One b) m sf)
viewLTree (Deep s (Three a b c) m sf) =
    ConsLTree a (Deep (s - size a) (Two b c) m sf)
viewLTree (Deep s (Four a b c d) m sf) =
    ConsLTree a (Deep (s - size a) (Three b c d) m sf)

{-# SPECIALIZE viewRTree :: FingerTree (Elem a) -> ViewRTree (Elem a) #-}
{-# SPECIALIZE viewRTree :: FingerTree (Node a) -> ViewRTree (Node a) #-}
viewRTree       :: Sized a => FingerTree a -> ViewRTree a
viewRTree EmptyT                = EmptyRTree
viewRTree (Single z)            = SnocRTree EmptyT z
viewRTree (Deep s pr m (One z)) = SnocRTree (pullR (s - size z) pr m) z
viewRTree (Deep s pr m (Two y z)) =
    SnocRTree (Deep (s - size z) pr m (One y)) z
viewRTree (Deep s pr m (Three x y z)) =
    SnocRTree (Deep (s - size z) pr m (Two x y)) z
viewRTree (Deep s pr m (Four w x y z)) =
    SnocRTree (Deep (s - size z) pr m (Three w x y)) z

{-# INLINE deep #-}
deep            :: Sized a => Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
deep pr m sf    =  Deep (size pr + size m + size sf) pr m sf

{-# INLINE node3 #-}
node3           :: Sized a => a -> a -> a -> Node a
node3 a b c     =  Node3 (size a + size b + size c) a b c

infixr 5 `consTree`
infixl 5 `snocTree`
{-# SPECIALIZE consTree :: Elem a -> FingerTree (Elem a) -> FingerTree (Elem a) #-}
{-# SPECIALIZE consTree :: Node a -> FingerTree (Node a) -> FingerTree (Node a) #-}
{-# SPECIALIZE consTree :: Segment a -> FingerTree (Segment a) -> FingerTree (Segment a) #-}
consTree        :: Sized a => a -> FingerTree a -> FingerTree a
consTree a EmptyT       = Single a
consTree a (Single b)   = deep (One a) EmptyT (One b)
-- As described in the paper, we force the middle of a tree
-- *before* consing onto it; this preserves the amortized
-- bounds but prevents repeated consing from building up
-- gigantic suspensions.
consTree a (Deep s (Four b c d e) m sf) = m `seq`
    Deep (size a + s) (Two a b) (node3 c d e `consTree` m) sf
consTree a (Deep s (Three b c d) m sf) =
    Deep (size a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
    Deep (size a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
    Deep (size a + s) (Two a b) m sf

{-# SPECIALIZE snocTree :: FingerTree (Elem a) -> Elem a -> FingerTree (Elem a) #-}
{-# SPECIALIZE snocTree :: FingerTree (Node a) -> Node a -> FingerTree (Node a) #-}
{-# SPECIALIZE snocTree :: FingerTree (Segment a) -> Segment a -> FingerTree (Segment a) #-}
snocTree        :: Sized a => FingerTree a -> a -> FingerTree a
snocTree EmptyT a       =  Single a
snocTree (Single a) b   =  deep (One a) EmptyT (One b)
-- See note on `seq` in `consTree`.
snocTree (Deep s pr m (Four a b c d)) e = m `seq`
    Deep (s + size e) pr (m `snocTree` node3 a b c) (Two d e)
snocTree (Deep s pr m (Three a b c)) d =
    Deep (s + size d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
    Deep (s + size c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
    Deep (s + size b) pr m (Two a b)


appendTree0 :: Sized a => FingerTree a -> FingerTree a -> FingerTree a
appendTree0 EmptyT xs =
    xs
appendTree0 xs EmptyT =
    xs
appendTree0 (Single x) xs =
    x `consTree` xs
appendTree0 xs (Single x) =
    xs `snocTree` x
appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
    Deep (s1 + s2) pr1 m sf2
  where !m = addDigits0 m1 sf1 pr2 m2

addDigits0 :: Sized a => FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)
addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

appendTree1 :: FingerTree (Node a) -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree1 EmptyT !a xs =
    a `consTree` xs
appendTree1 xs !a EmptyT =
    xs `snocTree` a
appendTree1 (Single x) !a xs =
    x `consTree` a `consTree` xs
appendTree1 xs !a (Single x) =
    xs `snocTree` a `snocTree` x
appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + s2) pr1 m sf2
  where !m = addDigits1 m1 sf1 a pr2 m2

addDigits1 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

appendTree2 :: FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree2 EmptyT !a !b xs =
    a `consTree` b `consTree` xs
appendTree2 xs !a !b EmptyT =
    xs `snocTree` a `snocTree` b
appendTree2 (Single x) a b xs =
    x `consTree` a `consTree` b `consTree` xs
appendTree2 xs a b (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` x
appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + s2) pr1 m sf2
  where !m = addDigits2 m1 sf1 a b pr2 m2

addDigits2 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

appendTree3 :: FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree3 EmptyT !a !b !c xs =
    a `consTree` b `consTree` c `consTree` xs
appendTree3 xs !a !b !c EmptyT =
    xs `snocTree` a `snocTree` b `snocTree` c
appendTree3 (Single x) a b c xs =
    x `consTree` a `consTree` b `consTree` c `consTree` xs
appendTree3 xs a b c (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` x
appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + s2) pr1 m sf2
  where !m = addDigits3 m1 sf1 a b c pr2 m2

addDigits3 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits3 m1 (One a) !b !c !d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) !c !d !e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) !d !e !f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) !e !f !g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

appendTree4 :: FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree4 EmptyT !a !b !c !d xs =
    a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs !a !b !c !d EmptyT =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d
appendTree4 (Single x) a b c d xs =
    x `consTree` a `consTree` b `consTree` c `consTree` d `consTree` xs
appendTree4 xs a b c d (Single x) =
    xs `snocTree` a `snocTree` b `snocTree` c `snocTree` d `snocTree` x
appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + size d + s2) pr1 m sf2
  where !m = addDigits4 m1 sf1 a b c d pr2 m2

addDigits4 :: FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
addDigits4 m1 (One a) !b !c !d !e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) !c !d !e !f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) !d !e !f !g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) !e !f !g !h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2

node2 :: Sized a => a -> a -> Node a
node2 a b = Node2 (size a + size b) a b
