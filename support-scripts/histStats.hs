import System.IO
import System.Environment
import Data.List.Split
import qualified Data.IntMap as IntMap

getPoint :: String -> (Int, Int)
getPoint line = (x,y)
    where readInt = read::String -> Int
          x = readInt . (!!0) . (splitOn " ") $ line
          y = readInt . (!!1) . (splitOn " ") $ line

getData :: [String] -> [(Int, Int)]
getData = map getPoint 

numPoints :: [(Int, Int)] -> Double
numPoints =  foldl (\acc (_,y) -> acc + (fromIntegral y)) 0.0 

average :: [(Int, Int)] -> Double
average points = 
        let sum = foldl (\ acc (x,y) -> acc + (fromIntegral x)* (fromIntegral y)) 0.0 points
            num = numPoints points   
         in sum/num

f :: (Int , Int) -> Double
f (x,y)
    | x >= 0 = 0
    | otherwise = fromIntegral y 

percentNeg :: [(Int, Int)] -> Double
percentNeg points =  
        let sum = foldl (\ acc p -> acc + (f p) ) 0.0 points
            num = foldl (\acc (_,y) -> acc + (fromIntegral y)) 0.0 points   
         in sum/num

stdDev :: [(Int, Int)] -> Double
stdDev points = 
        let avg = average points
            num = numPoints points
            squaredErrors = foldl (\acc (v,f)-> acc + (fromIntegral f)*(fromIntegral v - avg)^2 / num  ) 0.0 points
         in sqrt squaredErrors

histStats :: String -> IO()
histStats path = do
    contents <- readFile path 
    let contentsL  = lines $ contents 
        dataPoints = getData $ contentsL 
        num = numPoints dataPoints
     in print $ (path, average dataPoints, percentNeg dataPoints, stdDev dataPoints, num)


main = do
       args <- getArgs
       case args of 
        [path] -> histStats path
        otherwise -> print "invalied arguments"
