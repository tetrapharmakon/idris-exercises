module Vectoralgebra

import Data.Fin

data Vec : Nat -> Type -> Type where
  Nil : Vec Z a
  (::) : a -> Vec k a -> Vec (S k) a

append : Vec n a -> Vec m a -> Vec (n + m) a
append [] ys        = ys
append (x :: xs) ys = x :: append xs ys

len : Vec n a -> Nat
len [] = 0
len (x :: xs) = 1 + len xs

zipWith : (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f [] _                = []
zipWith f _ []                = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

fromList : (l : List elem) -> Vec (length l) elem
fromList []        = Nil
fromList (x :: xs) = x :: fromList xs

toList : Vec n a -> List a
toList []        = []
toList (x :: xs) = x :: toList xs

Matrix : Nat -> Nat -> Type -> Type
Matrix n m a = Vec n (Vec m a)
--                 | rows |
--                        | columns

empties : (m : Nat) -> Matrix m 0 a
empties Z     = []
empties (S k) = [] :: empties k

transpose : {m : Nat} -> Matrix n m a -> Matrix m n a
transpose {m} []                = empties m
transpose {m = Z} _             = []
transpose {m = (S k)} (x :: xs) = zipWith (::) x xs_trans
-- zipWith (::) v mat appends v as first vector in the matrix mat
  where
    xs_trans = transpose xs

map : (a -> b) -> Vec n a -> Vec n b
map f [] = []
map f (x :: y) = (f x) :: (map f y)

-- insert an element a at k-th entry
insert : a -> (k : Fin n) -> Vec n a -> Vec (S n) a
insert _ FZ []              impossible
insert _ (FS _) []          impossible
insert x FZ ys            = x :: ys
insert x (FS z) (y :: ys) = y :: insert x z ys

-- delete k-th entry
expunge : (k : Fin n) -> Vec (S n) a -> Vec n a
expunge FZ (x :: xs)     = xs
expunge (FS z) (x :: xs) = x :: expunge z xs

-- extract k-th entry
at : Vec n a -> (k : Fin n) -> a
at [] FZ             impossible
at [] (FS _)         impossible
at (x :: y) FZ     = x
at (x :: y) (FS z) = at y z

-- update k-th entry
updateAt : (k : Fin n) -> (f : a -> a) -> Vec n a -> Vec n a
updateAt FZ f (x :: xs)     = f x :: xs
updateAt (FS z) f (x :: xs) = x :: updateAt z f xs

-- proof del cristodedio
succKisKplusOne : (k : Nat) -> S k = plus k 1
succKisKplusOne Z     = Refl
succKisKplusOne (S n) = rewrite (plusCommutative n 1) in Refl

-- reverse a vector
reverse : Vec n a -> Vec n a
reverse {n = Z} []            = []
reverse {n = (S k)} (x :: xs) =
  rewrite (succKisKplusOne k) in append (reverse xs) (x :: [])

-- take' the head of a vector
head : Vec (S n) a -> a
head (x :: y) = x

-- take' the tail of a vector
tail : Vec (S n) a -> Vec n a
tail (x :: xs) = xs

-- take' the last element of a vector
last : Vec (S n) a -> a
last vec = head (reverse vec)

-- zip two vectors
zip : Vec n a -> Vec n b -> Vec n (a,b)
zip [] _ = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

-- take the longest initial segment of a vector satisfying p
-- note the use of dependent sum ** : you can not tell how long
-- the resulting vector will be.
takeWhile : (a -> Bool) -> Vec n a -> (k ** Vec k a)
takeWhile p []                         = (0 ** [])
takeWhile p (x :: xs)
  with (takeWhile p xs) | ( _ ** xs' ) = if (p x)
                                         then ( _ ** x :: xs')
                                         else ( _ ** xs' )

-- take' 2 [1,2,3,4] = [1,2]
-- but take' 5 [1,2,3,4] fails: lovely!
take' : (n : Nat) -> Vec (n + m) a -> Vec n a
take' Z []            = []
take' Z (x :: xs)     = []
take' (S k) (x :: xs) = x :: take' k xs

splitAt' : (n : Nat) -> Vec (n+m) a -> (Vec n a, Vec m a)
splitAt' Z []                  = ([], [])
splitAt' Z ys                  = ([], ys)
splitAt' (S k) (y::ys)
  with (splitAt' k ys) | (u,v) = (y :: u, v)

-- snd proof del cristodedio
sKKisKSK : (k : Nat) -> S (k + k) = k + (S k)
sKKisKSK Z     = Refl
sKKisKSK (S k) = rewrite (plusSuccRightSucc (S k) (S k)) in Refl

KSKissKK : (k : Nat) -> k + (S k) = S (k + k)
KSKissKK Z     = Refl
KSKissKK (S k) = rewrite (plusSuccRightSucc (S k) (S k)) in Refl

interleave : {n : Nat} -> Vec n a -> Vec n a -> Vec (n+n) a
interleave {n=Z} [] _                  = []
interleave {n=S k} (x :: xs) (y :: ys) =
  x :: rewrite (KSKissKK k) in (y :: interleave xs ys)