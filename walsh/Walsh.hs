module Walsh where

import Data.Matrix as M
import Data.Vector as V hiding (map)
import Data.Int (Int)
import Data.Bool (Bool (True, False))


-- fast Walsh-Hadamard Transform
-- produce a Hadmard matrix (natural ordering of rows)
-- not normalized
fWHT :: Int -> Matrix Int
fWHT 0 = identity 1
fWHT n = joinBlocks (r,r,r,-r) where
    r = fWHT (n-1)

-- two siblings
arithT, fRMT :: Int -> Matrix Int
arithT 0 = identity 1
arithT n = joinBlocks (r,z,-r,r) where
    r = arithT (n-1)
    z = M.zero (2^(n-1)) (2^(n-1))

fRMT 0 = identity 1
fRMT n = joinBlocks (r,z,r,r) where
    r = fRMT (n-1)
    z = M.zero (2^(n-1)) (2^(n-1))



getSpectrum :: Int -> [Int] -> Matrix Int
getSpectrum n ls = transpose (multStd (fWHT n) x) where
    x = colVector (V.fromList ls)


-- example from wiki
ex1 = getSpectrum 3 [1,0,1,0,0,1,1,0]
-- like Hadamard gate
ex2 = getSpectrum 1 [1,0]
ex3 = getSpectrum 1 [0,1]
-- example AND
ex4 = getSpectrum 2 [1,1,1,-1]
-- example OR
ex5 = getSpectrum 2 [1,-1,-1,-1]

-- what does walsh spectrum mean?



type Index = Int -- intervals
type Value = Int -- 1 or -1

-- n is 1-indexed (by convention)
-- i is 0-indexed
walshH :: Int -> Int -> (Index -> Value)
walshH k n i = let mls = toLists (fWHT k) in
    let v = V.fromList (mls !! (n-1)) in
        (V.!) v i 

-- print as a 2-row matrix
printWalshH :: (Index -> Value) -> Int -> Matrix Int
printWalshH wf n = M.fromLists [[0..(n-1)],values] where
    values = map wf [0..(n-1)]

-- to get different ordering of rows : sequency, dyadic, natural