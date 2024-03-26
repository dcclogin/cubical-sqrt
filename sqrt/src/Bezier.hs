module Bezier where

import Control.Monad (zipWithM)

type Point = [Float] 
type Dynamic a = Float -> a

-- Linear interpolation between two numbers.
lerp :: Float -> Float -> Dynamic Float
lerp a b t = (1 - t) * a + t * b

-- Line is a lerp between two points
line :: Point -> Point -> Dynamic Point
line = zipWithM lerp

-- Recursive Bézier curve calculation.
bezier :: [Point] -> Dynamic Point
bezier [p] = return p
bezier ps  = do p <- bezier (init ps)
                q <- bezier (tail ps)
                line p q

-- Example of berzier curve
c = bezier([[-200, -200], [-100, 100], [100, 100], [200, -200]])