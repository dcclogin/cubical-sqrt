module Bezier where

import Control.Monad (zipWithM)

type Point = [Float] 
type Dynamic a = Float -> a

-- Linear interpolation between two numbers.
lerp :: Float -> Float -> Dynamic Float
lerp a b t = (1 - t) * a + t * b

-- Wiki
-- deCasteljau :: Double -> [(Double, Double)] -> (Double, Double)
-- deCasteljau t [b] = b
-- deCasteljau t coefs = deCasteljau t reduced
--   where
--     reduced = zipWith (lerpP t) coefs (tail coefs)
--     lerpP t (x0, y0) (x1, y1) = (lerp t x0 x1, lerp t y0 y1)
--     lerp t a b = t * b + (1 - t) * a

-- Line is a lerp between two points
deCasteljau :: Point -> Point -> Dynamic Point
deCasteljau = zipWithM lerp

-- Recursive Bézier curve calculation.
bezier :: [Point] -> Dynamic Point
bezier [p] = return p
bezier ps  = do p <- bezier (init ps)
                q <- bezier (tail ps)
                deCasteljau p q

-- Example of berzier curve
c = bezier([[-200, -200], [-100, 100], [100, 100], [200, -200]])