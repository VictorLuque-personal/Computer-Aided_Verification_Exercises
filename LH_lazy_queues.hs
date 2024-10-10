-- Read Chapter 9 of the LH book about lazy queues
-- https://ucsd-progsys.github.io/liquidhaskell-tutorial/book.pdf

-- This are the exercises 9.5 and 9.6 taking the necessary definitions
-- from the book

module Exercise where
import Prelude hiding (replicate, take)

data SList a = SL { size :: Int, elems :: [a] }

{-@ size :: q:SList a -> {v:Nat | v = size q} @-}

{-@ measure realSize @-}
realSize      :: [a] -> Int
realSize []     = 0
realSize (_:xs) = 1 + realSize xs

{-@ data SList a = SL {
       size  :: Nat 
     , elems :: {v:[a] | realSize v = size}
     }
  @-}

{-@ type SListN a N = {v:SList a | size v = N} @-}


{-@ type NEList a = {v:SList a | size v > 0} @-}

{-@ type SListLE a N = {v:SList a | size v <= N} @-}

{-@ nil          :: SListN a 0  @-}
nil              = SL 0 []

{-@ cons         :: a -> xs:SList a -> SListN a {size xs + 1}   @-}
cons x (SL n xs) = SL (n+1) (x:xs)


{-@ tl           :: xs:NEList a -> SListN a {size xs - 1}  @-}
tl (SL n (_:xs)) = SL (n-1) xs

{-@ hd           :: xs:NEList a -> a @-}
hd (SL _ (x:_))  = x 

{-@ okList :: SListN String 1 @-}
okList = SL 1 ["a"]
okHd = hd okList -- accepted
--badHd = hd (tl okList) -- rejected

okQ = Q okList nil -- accepted, |front| > |back|
--badQ = Q nil okList -- rejected, |front| < |back|

data Queue a = Q  { front :: SList a
                  , back  :: SList a
                  }

{-@ data Queue a = Q {
       front :: SList a 
     , back  :: SListLE a (size front)
     }
  @-}

{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil  

{-@ example1Q :: QueueN _ 1 @-}
example1Q = Q (SL 1 [0]) nil

{-@ example2Q :: QueueN _ 2 @-}
example2Q = Q (1 `cons` (2 `cons` nil)) nil

--Start Alvaro
{-@ type QueueN a N = {v:Queue a | qsize v == N } @-}

{-@ measure qsize @-}
qsize :: Queue a -> Int
qsize (Q f b) = size f + size b

{-@ remove :: {qi:QueueN a {qsize qi} | qsize qi > 0} -> (a, QueueN a {qsize qi - 1}) @-}
remove (Q f b) = (hd f, makeq (tl f) b)

{-@ insert :: x:a -> qi:QueueN a {qsize qi} -> QueueN a {qsize qi + 1} @-}
insert e (Q f b) = makeq f (e `cons` b)

--{-@ replicate :: n:Nat -> a -> QueueN a n @-}
--replicate :: Int -> a -> Queue a  -- it does not work without this. Check https://github.com/ucsd-progsys/liquidhaskell/issues/1644
--replicate 0 _ = emp
--replicate n x = insert x (replicate (n-1) x)
--Finish Alvaro


--Exercise 9.5 ROTATE
{-@ makeq :: f:SList a -> b:SListLE a {size f + 1} -> QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise = Q (rot f b nil) nil

{-@ rot :: f:SList a -> b:SListN a {size f + 1} -> acc:SList a -> {v:SList a | size v = size f + size b + size acc } / [size f] @-}
rot f b acc
  | size f == 0 = hd b `cons` acc
  | otherwise = hd f `cons` rot (tl f) (tl b) (hd b `cons` acc)

--Exercise 9.6
{-@ emp :: QueueN _ 0 @-}
emp = Q nil nil

{-@ type QueueGE a N = {v:Queue a | N <= qsize v} @-}

{-@ take :: n:Nat -> q:QueueGE a n -> (QueueN a n, QueueN a {qsize q - n}) @-}
take :: Int -> Queue a -> (Queue a, Queue a)
take 0 q = (emp , q)
take n q = (insert x out , q'')
  where
    (x , q') = remove q
    (out, q'') = take (n-1) q'


