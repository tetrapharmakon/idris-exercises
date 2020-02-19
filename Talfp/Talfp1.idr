module Talfp1

main : IO ()
main = putStrLn "Hello, Taltech!"

data Nats = Ze | Su Nats

suma : Nats -> Nats -> Nats
suma Ze y = y
suma (Su x) y = Su (suma x y)

{- Implement the following function, which states that if you add the same value onto the front of
equal lists, the resulting lists are also equal: -}

same_cons : {xs : List a} ->
            {ys : List a} ->
            xs = ys       ->
            x :: xs = x :: ys
same_cons Refl = Refl

{- Define a type ThreeEq which expresses that three values must be equal -}

data ThreeEq : x -> y -> z -> Type where
  mkThreeEq : x -> ThreeEq x x x

{- Implement the following function which checks whether two lists are equal and returns a proof if so -}

checkEqList : DecEq a => (xs : List a) -> (ys : List a) -> Maybe (xs = ys)
checkEqList [] [] = Just Refl
checkEqList [] (x :: xs) = Nothing
checkEqList (x :: xs) [] = Nothing
checkEqList (x :: xs) (x :: ys) = ?ohle
