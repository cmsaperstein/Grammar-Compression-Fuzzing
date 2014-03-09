import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Cairo
import Data.Default.Class
import Data.Colour
import Data.Colour.SRGB
import Data.Colour.Names
import Control.Lens
import Control.Monad
import Data.List.Split
import Data.List
import System.Environment(getArgs)
import Debug.Trace


colors = map opaque [sRGB 0.026 0.31 0.494, sRGB 0.667 0.494 0.016, sRGB 0.667 0.184 0.016]

names = ["Kangaroo Method", "Edge Clustering", "LFS3"]

getPoint :: String -> (Int, Double)
getPoint line = (x,y)
    where readInt = read::String -> Int 
          readDouble = read::String -> Double
          x = readInt . (!!0) . (splitOn " ") $ line
          y = readDouble . (!!1) . (splitOn " ") $ line

getData :: [String] -> [(Int, Double)]
getData = map getPoint 

getPoints :: String -> [(Int, Double)] 
getPoints = getData . lines

toSeries (x,c,n) = plot_points_style .~ exes 3 1 (c)
           $ plot_points_values .~ x
           -- $ plot_points_title .~ n 
           $ def

chart :: [[(Int, Double)]] -> Renderable ()
chart dataSets = toRenderable layout
  where
     layout = layout_title .~ "Exact Method Time Performance"
          $ layout_plots .~ (map (toPlot . toSeries) (zip3 dataSets colors names))
          $ layout_x_axis . laxis_title .~ "Input Size (chars)" 
          $ layout_y_axis . laxis_title .~ "Time (ms)" 
          $ def

main =
    do        
       args <- getArgs
       case args of
           [] -> print "invalid arguments"
           otherwise ->
               do  
                  contentsList <- sequence $ map readFile args 
                  renderableToFile def (chart $ map getPoints contentsList) "out.png" >>
                    print "done"
                        
