module Lib where

import Text.Printf
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Bezier hiding (Point)

bezier2D :: [Point] -> Dynamic Point
bezier2D ps = ltop <$> bezier (ptol <$> ps)
  where ltop [x, y] = (x, y)
        ptol  (x, y) = [x, y]


-- Animation
data World = World {points :: [Point], 
                    time :: Float,
                    depth :: Int,
                    verbose :: Bool,
                    animating :: Bool}

initialWorld :: World
initialWorld = World {points=[(-200, -200)], 
                      time=0, 
                      depth=0, 
                      verbose=False, 
                      animating=True}


tick :: Float -> World -> World
tick dt world | animating world = world {time = time world + dt}
              | otherwise = world

key :: Event -> World -> World
key (EventKey (MouseButton LeftButton) Down _ p) world = world {points = points world ++ [p]}
key (EventKey (SpecialKey KeyUp) Down _ _) world = world {depth = depth world + 1 + 1}
key (EventKey (SpecialKey KeyDown) Down _ _) world = world {depth= depth world - 1 - 1}
key (EventKey (Char 'v') Down _ _) world = world {verbose=not (verbose world)}
key (EventKey (SpecialKey KeySpace) Down _ _) world = world {animating=not (animating world)}
key (EventKey (SpecialKey KeyDelete) Down _ _) world = world {points=init (points world)}
key _ world = world

dim' :: Color -> Color
dim' c = makeColor (r / k) (g / k) (b / k) a
  where (r, g, b, a) = rgbaOfColor c
        k = 1.5

picture :: World -> Picture
picture world = Pictures [
      go blue green (depth world) (points world),
      Color black $ Line $ c <$> ts,
      Color black $ Pictures $ [Translate x y $ ThickCircle w r | (x, y) <- points world],
      Color red $ Translate 225 250 $ Scale 0.175 0.175 $ Text $ printf "t = %.1f" t,
      Color green $ Translate cx cy $ ThickCircle w r
    ]
  where
    w = 2
    r = 5
    c = bezier2D $ points world
    ts = [0, 0.01 .. 1]
    t = (1 + cos (time world)) / 2
    (cx, cy) = c t
    go _ _ 0 _ = Blank
    go _ _ _ [_] = Blank
    go curveColor lineColor d ps = let
        go' = go (dim' curveColor) (dim' lineColor) (d - 1)
        a = bezier2D (init ps)
        b = bezier2D (tail ps)
        (ax, ay) = a t
        (bx, by) = b t
      in Pictures [
          go' (init ps),
          go' (tail ps),
          Color lineColor $ Line [a t, b t],
          if verbose world || d == 1 || length ps <= 3
            then Color curveColor $ Line $ a <$> ts
            else Blank,
          if verbose world || d == 1 || length ps <= 3 then Color curveColor $ Line $ b <$> ts else Blank,
          Color lineColor $ Translate ax ay $ ThickCircle w r,
          Color lineColor $ Translate bx by $ ThickCircle w r,
          Color lineColor $ Translate (lerp ax bx t) (lerp ay by t) $ ThickCircle w r
        ]
