module Talfp3

sumSquares : Integer -> Integer
sumSquares n = sum $ map (\x => x*x) [0..(n-1)]

helperino : String -> Integer
helperino x = the Integer (cast x)

interactive_addition : IO ()
interactive_addition = do
  text <- getLine
  case text of
       ""        => putStrLn "0"
       otherwise => putStrLn ((show . sum . (map helperino) . words) text)

dumbDivisors : Integer -> List Integer
dumbDivisors n = filter (\k => mod n k == 0) [1..n]

-- smart way is: generate divisors, but stop when they are more than 2
isPrime : Integer -> Bool
isPrime n = hasMany (dumbDivisors n)
  where
    hasMany [x,y] = True
    hasMany _ = False
