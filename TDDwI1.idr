module TDDwI1

-- Type-Driven Development w/ Idris
-- ~ E. Brady ~

-- Esercise set of Chapter 2 (iwth a few variations)

data Vec : Nat -> Type -> Type where
  Nil : Vec 0 a
  (::) : a -> Vec n a -> Vec (S n) a

implementation Eq a => Eq (Vec n a) where
  (==) [] [] = True
  (==) (x::xs) (y::ys) = (x == y) && xs ==  ys

implementation (Ord a, Eq a) => Ord (Vec n a) where
  compare [] _ = EQ
  compare [x] [y] = compare x y
  compare (x :: xs) (y :: ys) =
    if x == y
    then compare xs ys
    else compare x y

append : Vec n a -> Vec m a -> Vec (n + m) a
append [] ys        = ys
append (x :: xs) ys = x :: append xs ys

succKisKplusOne : (k : Nat) -> S k = plus k 1
succKisKplusOne Z     = Refl
succKisKplusOne (S n) = rewrite (plusCommutative n 1) in Refl

-- reverse a vector
reverse : Vec n a -> Vec n a
reverse {n = Z} []            = []
reverse {n = (S k)} (x :: xs) =
  rewrite (succKisKplusOne k) in append (reverse xs) (x :: [])

-- a function that checks if a list is a palyndrome (on lists)
palyList : Eq a => List a -> Bool
palyList xs = xs == reverse xs

test1 : Bool
test1 = palyList [1,0,0,0,1] == True

-- a function that checks if a string is palyndrome (case insensitive)
palyString : String -> Bool
palyString str with (toLower str) | lstr = lstr == reverse lstr

test2 : Bool
test2 = palyString "RaCeCar" == True

-- a function that checks if a list is a palyndrome (on vectors)
palyVec : Eq a => Vec n a -> Bool
palyVec vec = vec == reverse vec


-- a function that checks if a string is palyndrome if is less than n chars (case insensitive)
palyStringMoreTen : String -> Bool
palyStringMoreTen str
  with (toLower str) | lstr = if (length str < 10)
                              then False
                              else (lstr == reverse lstr)

palyStringMoreThan : Nat -> String -> Bool
palyStringMoreThan n str
  with (toLower str) | lstr = if (length str < n)
                              then False
                              else (lstr == reverse lstr)

-- returns # of words, and # of letters
counts : String -> (Nat, Nat)
counts str = (length (words str), length str)

-- returns ten greatest elements of list
top_ten : Ord a => List a -> List a
top_ten xs = take 10 (sort xs)

-- return how many elements have more than n chars
over_length : Nat -> List String -> Nat
over_length n strs = length $ filter (\x => length x > n) strs

-- repl interactive palyString and counts
main : IO ()
main = repl ">>> " (\x => show (palyString x) ++ "\n")

main2 : IO ()
main2 = repl ">>> " (\x => show (counts x) ++ "\n")
