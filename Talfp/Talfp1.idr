module Talfp1

main : IO ()
main = putStrLn "Hello, Taltech!"

data Nats = Ze | Su Nats

suma : Nats -> Nats -> Nats
suma Ze y = y
suma (Su x) y = Su (suma x y)
