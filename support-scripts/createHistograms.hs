import System.IO
import System.Environment
import Data.List.Split
import qualified Data.IntMap as IntMap

getPoint :: String -> Int
getPoint = readInt . (!!1) . (splitOn " ")
	where readInt = read::String -> Int

getData :: [String] -> [Int]
getData = map getPoint 

incrementCount :: IntMap.IntMap Int -> Int -> IntMap.IntMap Int
incrementCount m i 
	| IntMap.member i m = IntMap.adjust (+ 1) i m
	| otherwise = IntMap.insert i 1 m 

mkBins :: [Int] -> IntMap.IntMap Int
mkBins = foldl incrementCount IntMap.empty 

histString :: IntMap.IntMap Int -> String 
histString m = IntMap.foldlWithKey (\ s k x -> s ++ (show k) ++ " " ++ (show x) ++ "\n" ) "" m

mkHistogram :: String -> IO()
mkHistogram path = do
	contents <- readFile path 
	let contentsL = lines $ contents in
	    putStr . histString . mkBins . getData $ contentsL

main = do
    args <- getArgs	
    case args of
       [path] -> mkHistogram $ path 
       _ -> print "invalid arguments"
