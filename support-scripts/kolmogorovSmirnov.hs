import System.IO
import System.Environment
import Data.List.Split
import Data.List
import Data.Function
import qualified Data.IntMap as IntMap

getPoint :: String -> (Int, Int)
getPoint line = (x,y)
    where readInt = read::String -> Int
          x = readInt . (!!0) . (splitOn " ") $ line
          y = readInt . (!!1) . (splitOn " ") $ line

getData :: [String] -> [(Int, Int)]
getData = map getPoint 

getPoints :: String -> [(Int, Int)] 
getPoints = getData . lines

calcSize :: [(Int, Int)] -> Int
calcSize x = sum $ map snd x

normalize :: [(Int, Int)] -> [(Int, Double)]
normalize x = 
    let s = calcSize x 
     in map (\(f,v) -> (f, (fromIntegral v) / fromIntegral s)) x

mkCumDistribution :: [Int] -> [(Int, Double)] -> [Double]
mkCumDistribution domain points = 
    let pointsMap = IntMap.fromList points
        rawSample = map (\x -> IntMap.findWithDefault 0 x pointsMap) domain
     in scanl (+) 0 rawSample

ksTest :: String ->  String -> IO()
ksTest h1Path h2Path = do
    h1Contents <- readFile h1Path
    h2Contents <- readFile h2Path 
    let h1Points = getPoints h1Contents 
        h2Points = getPoints h2Contents 
        h1Size = fromIntegral . calcSize $ h1Points
        h2Size = fromIntegral . calcSize $ h1Points
        overallMin = fst $ minimumBy (compare `on` fst) (h1Points ++ h2Points)
        overallMax = fst $ maximumBy (compare `on` fst) (h1Points ++ h2Points)
        cumDist1 = mkCumDistribution [overallMin .. overallMax] (normalize h1Points)
        cumDist2 = mkCumDistribution [overallMin .. overallMax] (normalize h2Points)
        ksMetric = maximum $ map (\(x,y) -> abs (x-y)) (zip cumDist1 cumDist2)
        denom = sqrt $ (h1Size + h2Size) / (h1Size * h2Size) 
     in print $ (overallMin, overallMax, ksMetric / denom)

main = do
       args <- getArgs
       case args of 
        [h1path, h2path] -> ksTest h1path h2path
        otherwise -> print "invalied arguments"
