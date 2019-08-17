module Vectoralgebra

data Vec : Nat -> Type -> Type where
  Nil : Vec Z a
  (::) : a -> Vec k a -> Vec (S k) a

append : Vec n a -> Vec m a -> Vec (n + m) a
append [] ys        = ys
append (x :: xs) ys = x :: append xs ys

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

t_help : Vec m a -> Matrix m k a -> Matrix m (S k) a
t_help xs ys = zipWith (::) xs ys

transpose : {m : Nat} -> Matrix n m a -> Matrix m n a
transpose {m} []                = empties m
transpose {m = Z} _             = []
transpose {m = (S k)} (x :: xs) = t_help x xs_trans
  where
    xs_trans = transpose xs