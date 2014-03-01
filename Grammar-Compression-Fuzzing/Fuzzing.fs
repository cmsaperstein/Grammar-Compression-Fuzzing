namespace Fuzzing
open System.Collections.Generic
open System.Collections 
open Grammar
open Grammar.Utils
open SLSTree.Tree

open System.IO
open LFS.LFS

module Fuzzing = 
    /// perform a substitution to decrease the size of the grammar, using all branch substitutions. This is an O(|alphabet| n^2) exact answer
    let GrammarReduce1 lfsFun (xs:string) = 
        let mutable (minBaseRule, minOtherRules) = lfsFun xs
        let mutable minCompressionRatio = CompressionRatio minBaseRule minOtherRules
        let mutable subLoc = -1
        let mutable subSymbol = Nothing
        let subs = FindBranchSubstitutions (LiftSymbol xs)
        for loc in [0 .. subs.Length-1] do
            for sym in subs.[loc] do 
                let mutable substituted = (LiftSymbol xs)
                substituted.[loc] <- sym
                let (baseRule, otherRules) = lfsFun (convToString substituted)
                let compressionRatio = CompressionRatio baseRule otherRules
                if compressionRatio < minCompressionRatio then
                   minBaseRule <- baseRule 
                   minOtherRules <- otherRules
                   minCompressionRatio <- compressionRatio
                   subLoc <- loc
                   subSymbol <- sym
        (subLoc, SymToChar subSymbol)

    /// An O(n) approximation [doesn't work at all -- not even sure if it's linear]
    let EdgeJoiningReduce lfsFun (xs:string) =
        let (lfsBase, lfsRules) = lfsFun xs
        let (subLoc, subSymb, subScore) = FindFirstOrderSubstitution (Array.append (LiftSymbol xs) (List.toArray [End 0])) lfsBase
        (subLoc, SymToChar subSymb) 

    /// See how far we can expand the matches of some location to the left and right. The most expanded match is the beset substitution of the matches
    let FindBestExpansion allMatches (xs:string) (subLoc:int) (lfsBase:Symbol [])= 
        let mutable bestScore = 0
        let mutable bestMatchLoc = -1
        for matchLoc in allMatches do
            // if they are the same, there is no substitution to be made
            if not (xs.[subLoc] = xs.[matchLoc]) then
                let mutable leftWalk = 0
                let mutable rightWalk = 0
                let mutable leftWalkChanged = true
                let mutable rightWalkChanged = false
                while leftWalkChanged || rightWalkChanged do
                    if subLoc > matchLoc then
                       // make sure that the substitution being considered doesnt overlap with an already existing substitution
                       //if not(IsTerm lfsBase.[subLoc - leftWalk]) then
                          //leftWalkChanged <- false 
                       //if not(IsTerm lfsBase.[subLoc + rightWalk]) then
                          //rightWalkChanged <- false
                       if leftWalkChanged &&  // still expanding left
                          (matchLoc + rightWalk < subLoc - leftWalk) && // not double counting expanded area
                          (matchLoc-leftWalk > 0) && // still room to move left
                          (xs.[matchLoc-leftWalk-1] = xs.[subLoc-leftWalk-1]) then // still same character 1 step left of boundary
                            leftWalk <- leftWalk + 1
                       elif leftWalkChanged then
                            leftWalkChanged <- false
                       elif rightWalkChanged &&
                            (matchLoc + rightWalk < subLoc - leftWalk) &&
                            (subLoc + rightWalk < xs.Length - 1) &&
                            (xs.[matchLoc + rightWalk + 1] = xs.[subLoc + rightWalk + 1]) then
                             rightWalk <- rightWalk + 1
                       elif rightWalkChanged then
                            rightWalkChanged <- false
                    else
                       if leftWalkChanged &&  // still expanding left
                          (subLoc + rightWalk < matchLoc - leftWalk) && // not double counting expanded area
                          (subLoc-leftWalk > 0) && // still room to move left
                          (xs.[subLoc-leftWalk-1] = xs.[matchLoc-leftWalk-1]) then // still same character 1 step left of boundary
                            leftWalk <- leftWalk + 1
                       elif leftWalkChanged then
                            leftWalkChanged <- false
                       elif rightWalkChanged &&
                            (subLoc + rightWalk < matchLoc - leftWalk) &&
                            (matchLoc + rightWalk < xs.Length - 1) &&
                            (xs.[subLoc + rightWalk + 1] = xs.[matchLoc + rightWalk + 1]) then
                             rightWalk <- rightWalk + 1
                       elif rightWalkChanged then
                            rightWalkChanged <- false
                if leftWalk + rightWalk > bestScore then
                   bestScore <- leftWalk + rightWalk                   
                   bestMatchLoc <-  matchLoc
        (bestScore, bestMatchLoc)

    /// Index all character patterns of the form X_Y, XY_, and _XY, where X and Y are variables ranging over the alphabet, and _ is any character.
    /// For each terminal in the final base rule, search all matching X_Y, XY_, _YX patterns. _ represents the position of the terminal O(n)
    ///     For each hit, expand in each direct as much as possible while it is still a hit. 
    /// Choose the substitution that could be expanded the maximum size possible in both directions.

    (*
        Why is it possible for  BLAST reduce to increase the size of the derived grammar?    
        
    *)
    let GrammarBLASTReduceApprox (lfsFun:string -> Symbol [] * Symbol []) (xs:string) =
        let (lfsBase, lfsRules) = lfsFun xs
        // fill the search indexes
        let x_y  = new Dictionary<string, HashSet<int>>()
        let xy_  = new Dictionary<string, HashSet<int>>()
        let _xy  = new Dictionary<string, HashSet<int>>()
        for i in [0..xs.Length-1] do
            if i>0 && i < xs.Length-1 then
                let pattern = (string xs.[i-1]) + string(xs.[i+1])
                if not(x_y.ContainsKey(pattern)) then
                    x_y.Add(pattern, new HashSet<int>())
                x_y.[pattern].Add(i) |> ignore
            if i>1 then
                let pattern = (string xs.[i-2]) + string(xs.[i-1])
                if not(xy_.ContainsKey(pattern)) then
                    xy_.Add(pattern, new HashSet<int>())
                xy_.[pattern].Add(i) |> ignore
            if i<xs.Length-2 then
                let pattern = (string xs.[i+1]) + string(xs.[i+2])
                if not(_xy.ContainsKey(pattern)) then
                    _xy.Add(pattern, new HashSet<int>())
                _xy.[pattern].Add(i) |> ignore
        // find the best scoring match
        let mutable bestScore = 0
        let mutable bestMatchLoc = -1
        let mutable bestSubLoc = -1
        // for every terminal character in the final rule, expand locations of similar areas that difffer by 1 character
        // the area that can be expanded by the most is the best scoring match
        for i in [0..lfsBase.Length-1] do
            if IsTerm lfsBase.[i] then
                let mutable allMatches = new HashSet<int>()
                if i>0 && i < xs.Length-1 then
                    let pattern = (string xs.[i-1]) + string(xs.[i+1])
                    let x_yMatches = x_y.[pattern]
                    allMatches.UnionWith(x_yMatches)
                if i>1 then
                    let pattern = (string xs.[i-2]) + string(xs.[i-1])
                    let xy_Matches = xy_.[pattern]
                    allMatches.UnionWith(xy_Matches)
                if i<xs.Length-2 then
                    let pattern = (string xs.[i+1]) + string(xs.[i+2])
                    let _xyMatches = _xy.[pattern]
                    allMatches.UnionWith(_xyMatches)
                let (score, matchLoc) = FindBestExpansion allMatches xs i lfsBase
                if score > bestScore then
                    bestScore <- score
                    bestMatchLoc <- matchLoc
                    bestSubLoc <- i 
        if bestMatchLoc > 0 then
            (bestSubLoc, xs.[bestMatchLoc])
        else 
            (bestSubLoc, ' ')


