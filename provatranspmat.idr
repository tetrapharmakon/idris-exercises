import Data.Vect

replicateVect : (n : Nat) -> (x : a) -> Vect n a
replicateVect Z x     = []
replicateVect (S k) x = x :: replicateVect k x

transposeEmpty : Vect n (Vect 0 a)
transposeEmpty = replicate _ []

transposeMatrix' : (x : Vect n a) -> Vect n (Vect m a) -> Vect n (Vect (S m) a)
transposeMatrix' []        []        = []
transposeMatrix' (x :: xs) (y :: ys) = (x :: y) :: transposeMatrix' xs ys

transposeMatrix : Vect n (Vect m a) -> Vect m (Vect n a)
transposeMatrix []        = transposeEmpty
transposeMatrix (x :: xs) = let xsTr = transposeMatrix xs in
                             transposeMatrix' x xsTr