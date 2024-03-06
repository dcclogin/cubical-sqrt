{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}


module Sqrt where
import Data.List
import Numeric.AD
import Numeric.LinearAlgebra
-- import qualified Numeric.AD.Mode.Reverse as R
-- import qualified Numeric.AD.Mode.Reverse.Double as RD

f :: Fractional a => a -> a
f x = x + 1

-- Takes a function f and generates the Carleman matrix of f.
carleman :: Int ->  [[Double]]
carleman size = [[ aux j k | k <- [0..size-1]] | j <- [0..size-1]]
    where
    aux j k = if k < length (diffs (\x -> f x ^ j) 0) 
              then (diffs (\x -> f x ^ j) 0 !! k) / product [1.. fromIntegral k]
              else 0

-- To find square root we can use Denman–Beavers iteration.
test1 = sqrtm (fromLists (carleman 3))
