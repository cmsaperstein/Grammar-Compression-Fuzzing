namespace Fuzzing
open System.Collections.Generic
open System.Collections 
open Grammar
open Grammar.Utils
open SLSTree.Tree

open System.IO
open LFS.LFS

module Fuzzing = 
    
    /// Perform the character substitution described by the output of a grammar fuzzing algorithm
    let PerformSub (subLoc:int, subChar:char) (xs:string) = 
        if subLoc >= 0 then
           let sb = new System.Text.StringBuilder(xs)
           sb.[subLoc] <- subChar
           sb.ToString()
        else 
           xs

    let UpdateNodeSubstitutions slstree nodeRef (substitutions: HashSet<Symbol>[]) = 
        let node = GetNode slstree nodeRef
        let newSubs = node.children.Keys |> set 
        for cRef in node.children.Values do
            // internal node corresponding to the string before the branch
            let c = GetNode slstree cRef
            // append the substitutions at each position where the string represented by node occurs
            substitutions.[c.beg_i].UnionWith(newSubs)
        substitutions

    /// All possible substitutions that could reduce the size of the grammar. It is sufficient to look at alternate starting characters
    /// for different branch points in the tree
    let FindBranchSubstitutions (xs:Symbol []) = 
        let slstree = MKSLSTree xs
        let mutable substitutions = Array.create slstree.data.Length (new HashSet<Symbol>())
        // prevent all cells of substitutions from pointing to the same hashset
        substitutions <- Array.map (fun value -> new HashSet<Symbol>()) substitutions 

        // behavior around root is an intersting question
        // at the moment, it is assumed that if a substitution at a child of the root could help, then another substitution exists elsewhere in the tree
        // that does the exact same thing
        for nodeRef in [1 .. slstree.nodes.Length-1] do
            UpdateFromChildren slstree nodeRef 
            UpdateNodeSubstitutions slstree nodeRef substitutions |> ignore
        // remove substitutions that replace the original element with itself
        Array.mapi (fun i (v:HashSet<Symbol>) -> v.Remove slstree.data.[i] |> ignore; v) substitutions


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

    
    /// Takes an input that describes the edges in a cluster and the depth at which to examine these edges
    let ClusterEdgeList slstree nodeRef cluster depth lfsBase= 
        let node = GetNode slstree nodeRef
        let clusters = new Dictionary<Symbol, List<Symbol>>()
        for edgeBeg in cluster do
            let edgeNode = GetNode slstree node.children.[edgeBeg]
            // if depth is still indexing a piece of this edge
            if depth < edgeNode.end_i - edgeNode.beg_i then
               let edgeChar = slstree.data.[edgeNode.beg_i + depth]
               // do not add nonexistant characters to the clusters
               match edgeChar with 
               | End _ -> () 
               | _ ->
               // mark this edge as being part of the cluster with character at depth of edgeChar
                   if clusters.ContainsKey edgeChar then
                      clusters.[edgeChar].Add(edgeBeg)
                   else
                      let singletonCluster = new List<Symbol> ()
                      singletonCluster.Add(edgeBeg)
                      clusters.Add(edgeChar, singletonCluster)

        // only maintain clusters that have more than one element and contain a leaf element that refers to a nondead area
        let aliveClusters = new List<List<Symbol>>()
        let mutable hasBeenAdded = false
        for cluster in clusters.Values do 
            hasBeenAdded <- false
            if cluster.Count > 1 then
               for begChar in cluster do 
                   if not (hasBeenAdded) then
                     let child = GetNode slstree node.children.[begChar]
                     if IsLeaf slstree node.children.[begChar] && not(IsDeadArray lfsBase child.beg_i) then
                        aliveClusters.Add(cluster)
                        hasBeenAdded <- true
        aliveClusters 

    /// Find the deepest point up to which, besides the first symbol, two edges are identical
    let FindBestSubForNode slstree nodeRef (lfsBase:Symbol []) = 
        let node = GetNode slstree nodeRef
        node.children.Remove(End 0) |> ignore
        let mutable depth = 1
        let mutable clusters = new List<List<Symbol>>()
        clusters <- ClusterEdgeList slstree nodeRef node.children.Keys depth lfsBase
        // take the depth to the next level and attempt to cluster
        while clusters.Count > 1 do
            depth <- depth + 1
            let mutable newClusters = new List<List<Symbol>>()
            // subcluster each existing cluster
            for cluster in clusters do 
                newClusters.AddRange(ClusterEdgeList slstree nodeRef cluster depth lfsBase)
            // if there are no new clusters at the next level, just terminate the loop with 1 element in clusters
            if newClusters.Count > 0 then
                clusters <- newClusters
            else
               clusters.RemoveRange(1, clusters.Count-1)
        if clusters.Count = 0 then         
            (0, -1, Nothing)
        else
            let mutable subLoc = -1
            let mutable subSymbol = Nothing
            let mutable chosenLeaf = Nothing
            // find the shortest leaf as the destination of the substitution 
            for begEdge in clusters.Item 0 do
                let edgeRef = node.children.[begEdge]
                // the substitution location should be on a leaf not originally replaced in the lfs pass
                if IsLeaf slstree edgeRef then
                   let candidateLoc = (GetNode slstree edgeRef).beg_i
                   if not(IsDeadArray lfsBase candidateLoc) then
                      subLoc <- (GetNode slstree edgeRef).beg_i
                      chosenLeaf <- begEdge
            // find any other node besides the chosen leaf
            for begEdge in clusters.Item 0 do
                if not(begEdge = chosenLeaf) then
                    subSymbol <- begEdge
            (depth,  subLoc, subSymbol)

    /// Do a first order approximation that only looks one node deep 
    let FindFirstOrderSubstitution (xs : Symbol []) (lfsBase : Symbol []) = 
        let slstree = MKSLSTree xs
        let mutable bestDepth = 0
        let mutable bestSubLoc = -1
        let mutable bestSubSymb = Nothing
        for nodeRef in [0 .. slstree.nodes.Length-1] do 
            let (subDepth, subLoc, subSymb) = FindBestSubForNode slstree nodeRef lfsBase
            if subDepth > bestDepth then
                bestDepth <- subDepth
                bestSubLoc <- subLoc
                bestSubSymb <- subSymb
        (bestSubLoc, bestSubSymb, bestDepth)

    
    
    /// An O(n) approximation using Edge Joining
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


