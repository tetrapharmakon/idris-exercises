module MatrixProd where

import Data.List

matrixProduct :: Num a => [[a]] -> [[a]] -> [[a]]
matrixProduct as bs = [[f (as !! i) (bs' !! j) | j <- [0..lb]] | i <- [0..la]]
  where
    bs' = transpose bs
    la = length as - 1
    lb = length (head bs) - 1
    f x y = sum $ zipWith (*) x y


a = [[1,2,3],[4,5,6]]
b = [[0,1],[1,1],[2,2]]
c = [[0,1],[1,0]]
