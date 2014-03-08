open System.IO
open Grammar
open Grammar.Utils
open SLSTree.Tree
open LFS.LFS
open Fuzzing.Fuzzing
open FsCheck

let randString (rand:System.Random) size =  
    let sb = new System.Text.StringBuilder()
    for i in [0 .. size-1] do
        let randChar = rand.Next(65,125) |> char
        sb.Append(randChar) |> ignore
    sb.ToString()

let randSub (rand:System.Random) dummyFun (str:string) = 
    let size = str.Length
    let randChar = rand.Next(65,125) |> char
    let randLoc = rand.Next(0,size-1)
    (randLoc, randChar)

let identity dummyFun (str:string) = 
    (-1, ' ')

let stringSliceGenerator (inString:string) (rand:System.Random) size = 
    let startLoc = rand.Next(0,inString.Length - size) 
    inString.[startLoc..startLoc + size-1] 

let rec indexesAllSubstringsH (tree:SLSTree.SLSTree) (s:string) i j finish = 
    if i >= finish then 
        true
    elif j >= finish then
        indexesAllSubstringsH tree s (i+1) (i+1) finish
    elif Contains tree (LiftSymbol s.[i..j]) then
        indexesAllSubstringsH tree s i (j+1) finish
    else 
        printfn "falsifying case is:%s" s.[i..j]
        false

let slstreeIndexesAllSubstringsBesides (xs:string) = 
    let slstree = MKSLSTree (LiftSymbol xs)
    let beg = 0
    let len = xs.Length
    (indexesAllSubstringsH slstree xs 0 0 beg) && (indexesAllSubstringsH slstree xs (beg+len) (beg+len) xs.Length)

let slstreeCanCreate (xs:string) = 
    let tree = MKSLSTree (LiftSymbol xs)
    true

let checkSLSTree () = 
    Check.One({Config.Quick with MaxTest = 10000}, slstreeIndexesAllSubstringsBesides)
    // check if a huge slstree can be created with no error
    Check.One({Config.Quick with MaxTest = 10
                                 EndSize = 1000000
                                 StartSize = 100000 }, slstreeCanCreate)

let checkLFSNoError (xs:string) = 
    let (baseRule, otherRules) = LFS2 xs
    printfn "%f" (CompressionRatio baseRule otherRules)
    true

let checkLFSCorrect (xs:string)  = 
    xs = Decompress (LFS2 xs)

let checkLFS () = 
    Check.One({Config.Quick with MaxTest = 100
                                 EndSize = 100000}, checkLFSNoError)
    Check.One({Config.Quick with MaxTest = 10000}, checkLFSCorrect)

let lfsCompression lfsFun (xs:string) =
    let (baseRule, otherRules) = lfsFun xs
    let sizeX = xs.Length
    let compressionY = CompressionRatio baseRule otherRules
    (sizeX, compressionY)

let lfsTime lfsFun (xs:string) = 
    let stopWatch = System.Diagnostics.Stopwatch.StartNew() 
    let (baseRule, otherRules) = lfsFun xs
    stopWatch.Stop()
    let timeElapsedY = stopWatch.Elapsed.TotalMilliseconds
    let sizeX = xs.Length
    (sizeX, timeElapsedY)

let grammarReduceTime reduceFun (xs:string) = 
    let stopWatch = System.Diagnostics.Stopwatch.StartNew() 
    let (subLoc, subSymbol) = reduceFun xs
    stopWatch.Stop()
    let timeElapsedY = stopWatch.Elapsed.TotalMilliseconds
    let sizeX = xs.Length
    (sizeX, timeElapsedY)

let graphTimeLFS lfs textGenerator fileName =
    let outFile = new StreamWriter("C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\data\\" + fileName)
    let maxSize = 100000
    let testsPerSize = 1 
    let step = 1000
    for size in [step .. step .. maxSize] do
        for test in [0 .. testsPerSize] do 
            let (sizeX, timeY) =  textGenerator size |> lfsTime lfs
            outFile.WriteLine( (string sizeX) + " " + (string timeY))
    outFile.Close()

let graphTimeGrammarReduce reduceFun textGenerator fileName =
    let outFile = new StreamWriter("C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\data\\" + fileName)
    let maxSize = 100000 
    let testsPerSize = 1 
    let step = 1000 
    for size in [step .. step .. maxSize] do
        for test in [1 .. testsPerSize] do 
            let (sizeX, timeY) =  textGenerator size |> grammarReduceTime reduceFun
            outFile.WriteLine( (string sizeX) + " " + (string timeY))
            outFile.Flush()
    outFile.Close()

let graphCompressionRatioLFS lfsFun textGenerator fileName =
    let outFile = new StreamWriter("C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\data\\" + fileName)
    let maxSize = 100000
    let testsPerSize = 1 
    let step = 1000
    for size in [step .. step .. maxSize] do
        for test in [0 .. testsPerSize] do 
            let (sizeX, compressionY) =  textGenerator size |> lfsCompression lfsFun 
            outFile.WriteLine( (string sizeX) + " " + (string compressionY))
    outFile.Close()

let graphKangarooTimeEstimate textGenerator fileName =
    let outFile = new StreamWriter("C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\data\\" + fileName)
    let maxSize = 50000
    let testsPerSize = 1 
    let step = 1000
    for size in [step .. step .. maxSize] do
        for test in [0 .. testsPerSize] do 
            let (baseRule, otherRules) =  textGenerator size |> LFS1 
            let kangarooTime = (CountTerm baseRule) * (CountEnd otherRules)
            outFile.WriteLine( (string size) + " " + (string kangarooTime))
    outFile.Close()

let graphSizeVsNumReductions reduceFun lfsFun textGenerator fileName size =
    let outFile = new StreamWriter("C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\data\\" + fileName)
    let maxReductions = 10
    let trials = 1000
    for i in [0 .. trials] do
        let mutable input:string = textGenerator size
        let mutable debugInput = input
        let (startBaseRule, startOtherRules) = lfsFun input 
        let mutable lastGrammarSize = CountAlive startBaseRule + CountAlive startOtherRules
        for reduction in [0 .. maxReductions] do 
            let (subLoc, subChar) = reduceFun input 
            if subLoc >= 0 then
               let sb = new System.Text.StringBuilder(input)
               sb.[subLoc] <- subChar
               input <- sb.ToString()
            let (baseRule, otherRules) = lfsFun input 
            let newSize = CountAlive baseRule + CountAlive otherRules
            outFile.WriteLine( (string reduction) + " " + (lastGrammarSize - newSize |> string))
            lastGrammarSize <- newSize
            debugInput <- input
        outFile.Flush()
    outFile.Close()

let dataGeneration() = 
    let folder = "C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\texts\\"
    let shakespeareText = File.ReadAllText("C:\\Users\\Craig\\Desktop\\data\\shakespeare.txt")
    let shakespeareGenerator = stringSliceGenerator shakespeareText
    let size = 5000
    let numTrials = 1000

    let rand = System.Random()

    for trial in [0 .. numTrials] do
        for textGen, textName in [(shakespeareGenerator rand,"shakespeare"); (randString rand, "rand") ] do
            let text = textGen size
            let trialName = textName + "_" +  (string trial)
            let outFile = new StreamWriter(folder + trialName)
            outFile.Write(text)
            outFile.Close()
    ()

let experimentPercentageCharFuzzing() = 
    let inFolder = "C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\texts\\"
    let outFolder = "C:\\Users\\Craig\\Documents\\Cambridge\\CS\\Part II Project\\fuzzing-data\\"
    let files = Directory.GetFiles(inFolder)

    let rand = new System.Random()
    let numReductions = 20

    for lfsFun, lfsName in [(LFS1, "lfs1"); (LFS2, "lfs2"); (LFS3, "lfs3")] do
        for reduceFun, reduceName in [(randSub rand, "randomSub"); (EdgeJoiningReduce,"edgeJoiningReduce"); ] do
            let description = lfsName + "_" +  reduceName + "_"  
            let outShake = new StreamWriter(outFolder + description + "shake")
            let outRand = new StreamWriter(outFolder + description + "rand")
            for file in files do
                let mutable text = (new StreamReader(file)).ReadToEnd()
                let originalSize =  lfsFun text |> GrammarSize
                for i in [1..numReductions] do
                    text <- PerformSub (reduceFun lfsFun text) text
                let difference = originalSize - (lfsFun text |> GrammarSize ) 
                if file.Contains("shake") then 
                    outShake.WriteLine(string difference)
                else if file.Contains("rand") then 
                    outRand.WriteLine(string difference)
            outShake.Close()
            outRand.Close()
    ()
let longTests() = 
    printfn "starting tests"
    let shakespeareText = File.ReadAllText("C:\\Users\\Craig\\Desktop\\data\\shakespeare.txt")
    let shakespeareGenerator = stringSliceGenerator shakespeareText
    let rand = new System.Random()
    
    printfn "testing grammar fuzzing time performancce"
    for reduceFun, reduceName in [(EdgeJoiningReduce,"edgeJoiningReduce"); (GrammarBLASTReduceApprox, "blastReduce")] do
        for textGen, textName in [(shakespeareGenerator rand,"shakespeare"); (randString rand, "rand") ] do
            let description = reduceName + "_lfs1_" + "time" + "_" + textName
            graphTimeGrammarReduce (reduceFun LFS1) textGen description
            printfn "completed:%s" description
    
    printfn "starting time tests"
    for lfsFun, lfsName in [(LFS1, "lfs1"); (LFS2, "lfs2"); (LFS3, "lfs3")] do
        for textGen, textName in [(randString rand, "rand"); (shakespeareGenerator rand,"shakespeare")] do
            let description = lfsName + "_" + "time" + "_" + textName
            graphTimeLFS lfsFun textGen description
            printfn "completed:%s" description
    
    printfn "starting compression ratio tests"
    for lfsFun, lfsName in [(LFS1, "lfs1"); (LFS2, "lfs2"); (LFS3, "lfs3")] do
        for textGen, textName in [(randString rand, "rand"); (shakespeareGenerator rand,"shakespeare")] do
            let description = lfsName + "_" + "compressionRatio" + "_" + textName
            graphCompressionRatioLFS lfsFun textGen description
            printfn "completed:%s" description
    
    printfn "starting delta string tests"    
    for lfsFun, lfsName in [(LFS1, "lfs1"); (LFS2, "lfs2"); (LFS3, "lfs3")] do
        for reduceFun, reduceName in [(GrammarReduce1, "perfectReduce"); (EdgeJoiningReduce,"edgeJoiningReduce"); (GrammarBLASTReduceApprox, "blastReduce")] do
            for textGen, textName in [(randString rand, "rand"); (shakespeareGenerator rand,"shakespeare")] do
                let description = (lfsName + "_" +  reduceName + "_" + textName )
                graphSizeVsNumReductions (reduceFun lfsFun) lfsFun textGen description 30
                printfn "completed:%s" description
      
    printfn "starting large delta tests"
    for lfsFun, lfsName in [(LFS1, "lfs1"); (LFS2, "lfs2"); (LFS3, "lfs3")] do
        for reduceFun, reduceName in [(randSub rand, "randomSub"); (EdgeJoiningReduce,"edgeJoiningReduce"); (GrammarBLASTReduceApprox, "blastReduce")] do
            for textGen, textName in [(randString rand, "rand"); (shakespeareGenerator rand,"shakespeare")] do
                let description = lfsName + "_" +  reduceName + "_" + textName + "_large" 
                graphSizeVsNumReductions (reduceFun lfsFun) lfsFun textGen description 15
                printfn "completed:%s" description
    
[<EntryPoint>]
let main argv = 
    let inString1 = "abcdabcd_abab_cd" 
    printfn "Now Showing a demo of different aspects of the project"
    printfn "----------------------------------------------------------------"
    printfn "Starting with the grammar compression algorithms"
    printfn "The initial string is: %s" inString1
    for lfsFun, lfsName in [(LFS1, "LFS1"); (LFS2, "LFS2"); (LFS3, "LFS3")] do
        printfn "%s:" lfsName
        lfsFun inString1 |> RulesPairToString |> printfn "%s"
    printfn "----------------------------------------------------------------"
    let inString2 = "abcabcqbc" 
    printfn "Now showing the grammar fuzzing algorithms"
    printfn "The initial string is: %s\n" inString2
    for reduceFun, reduceName in [(GrammarReduce1, "Perfect Fuzz"); (EdgeJoiningReduce,"Edge Clustering Fuzz"); (GrammarBLASTReduceApprox, "BLAST Fuzz")] do
        printfn "When this input string is fuzzed with %s, the result is:" reduceName 
        let (subLoc, subChar) = reduceFun LFS1 inString2
        printfn "at location %d the the character %c is substituted" subLoc subChar
        PerformSub (subLoc, subChar) inString2 |> printfn "the result of this is: %s\n"
    0