module Main (main) where
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game

import Lib

main :: IO ()
main = play (InWindow "Bézier" (600, 600) (0,  0))
       white 50 initialWorld
       picture key tick
