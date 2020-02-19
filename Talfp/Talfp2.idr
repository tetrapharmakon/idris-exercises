module Talfp2

main : IO ()
main = putStrLn "asdwasd"

myReverse : List t -> List t
myReverse [] = []
myReverse (x :: xs) = myReverse xs ++ [x]

-- what's the difference in timing?
myReverse' : List t -> List t
myReverse' xs = foldl (\acc, x => x :: acc) [] xs

revString : String -> String
revString = (pack . myReverse . unpack)

palyndrome : String -> Bool
palyndrome xs = xs == revString xs

myCycle : List ty -> Nat -> List ty
myCycle [] _ = []
myCycle _ Z = []
myCycle xs (S k) = xs ++ myCycle xs k

odds : List t -> List t
odds [] = []
odds [x] = []
odds (x :: y :: zs) = y :: odds zs

evens : List t -> List t
evens [] = []
evens [x] = [x]
evens (x :: y :: zs) = x :: evens zs

deal : List t -> (List t, List t)
deal xs = (odds xs, evens xs)

takeThree : Ord a => List a -> List a
takeThree xs = if length xs < 3 then xs else pickEm xs
  where
    pickEm xs = take (the Nat 3) $ sort xs
    length [] = 0
    length (x :: xs) = 1 + length xs

myUnzip : List (a,b) -> (List a, List b)
myUnzip = foldr (\(x, y), (xs, ys) => (x::xs, y::ys)) ([],[])
