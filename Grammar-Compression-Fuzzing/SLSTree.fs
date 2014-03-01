namespace SLSTree
open System.Collections.Generic
open System.Collections 
open Grammar.Utils
open Grammar
open STree
open STree.Tree

///   <summary> Represents a node in a lazy sparse suffix tree. The advantage is in specifying the minimum, maximum, and number of beginnning positions.
///   This is enough information to determine if an internal node corresponds to an overlapping occurence, and if so, what the locations of the overlaps are.
///   </summary>
///  <param name = "beg_i"> Beginning position in the input that this node indexes </param>
///  <param name = "end_i"> End position in the input that this node indexes </param>
///  <param name = "s_link"> Suffix links in the suffix tree </param>
///  <param name = "parent"> A link to the parent node for convenience. This is useful in node deletion, but not strictly necessary </param>
///  <param name = "min_beg_pos"> The minimum beginning position of the occurence </param>
///  <param name = "max_beg_pos"> The maximum beginning position of the occurence </param>
///  <param name = "num_beg_pos"> The number of beginning positions of the occurence </param>
///  <param name = "pathlen"> Length of the string this node represents </param>
///  <param name = "children"> Children nodes in the suffix tree </param>

type LNode =  {
    mutable beg_i : int
    mutable end_i : int 
    mutable s_link : int 
    mutable parent : int 
    mutable min_beg_pos : int
    mutable max_beg_pos : int
    mutable num_beg_pos : int
    mutable pathlen : int
    mutable children : Dictionary<Symbol, int> 
    } 

///  <summary> A lazy sparse suffix tree. Sparse in the sense it does not represent and substituted grammar symbols. Lazy in that nodes are only updated when they are 
///  considered for removal. 
///  </summary>
///  <param name = "data"> Input string being indexed by the tree </param>
///  <param name = "nodes"> The structure of the tree </param>
///  <param name = "bins"> Indexing internal nodes by the path lengths they represent. The longest repeated substring is the bin with the highest int index </param>

type SLSTree = {
    mutable data : Symbol [] 
    nodes : LNode []
    mutable bins : Dictionary<int, List<int> > // first arg is pathlen, second is a reference to a list of nodes with that pathlen 
    }

module Tree = 
    /// mark a part of the output as dead
    let MarkNothing slstree i len = 
        Array.fill slstree.data i len Nothing

    /// mark the specified index as a nonterminal symbol
    let MarkNonterm slstree i nonterm = 
        slstree.data.[i] <- nonterm

    /// gets the node by the node reference
    let GetNode slstree nodeRef = 
        slstree.nodes.[nodeRef]
     
    /// determines if the node is a leaf
    let IsLeaf slstree nodeRef = 
        (GetNode slstree nodeRef).end_i = slstree.data.Length

    /// determines whether the location can be replaced
    let IsDead slstree i = 
        match slstree.data.[i] with
        |    Term c -> false 
        |    End i -> false 
        |    _  -> true 
    
    let IsDeadArray (lfsBase:Symbol []) i = 
        match lfsBase.[i] with
        |    Term c -> false 
        |    End i -> false 
        |    _  -> true 

    /// deletes a node from the suffix tree 
    let DeleteNode slstree nodeRef = 
        let node = GetNode slstree nodeRef
        node.beg_i <- -3
        node.end_i <- -3

    /// gives a string representation of a node in the suffix tree 
    let rec nodeToString slstree nodeRef whitespace = 
        let current = GetNode slstree nodeRef 
        if nodeRef = 0 then
           printfn "%s" "."
        else 
           printfn "%s(%d,%d) [%d, %d, %d, %d]" whitespace current.beg_i current.end_i current.min_beg_pos current.max_beg_pos current.num_beg_pos current.pathlen
        for c in current.children.Keys do
           printfn "%s%A(%d)"  whitespace c current.children.[c]
           nodeToString slstree current.children.[c] (whitespace + "   ")

    // gives a string representation of the tree
    let TreeToString slstree = 
         nodeToString slstree 0 ""

    /// translates a suffix tree node to a lazy sparse suffix tree node
    let ToLNode (stree:STree.STree) (node:STree.Node) = 
        {beg_i = node.beg_i;
         end_i = node.end_i; 
         s_link = node.s_link; 
         parent = node.parent;
         min_beg_pos = stree.data.Length; 
         max_beg_pos = 0; 
         num_beg_pos = 0; 
         pathlen = 0; 
         children = node.children;}

    /// Indexes the internal nodes of the lazy sparse suffix tree by the path lengths they represent
    let setBins slstree = 
       let nodesToCheck = new Stack<int>()
       nodesToCheck.Push(0)
       while nodesToCheck.Count > 0 do
           let nodeRef = nodesToCheck.Pop()
           let node = GetNode slstree nodeRef
           if nodeRef = 0 then
              node.pathlen <- 0
           // if this is an internal node, corresponding to a repeated factor
           if node.children.Count > 1 && node.pathlen > 1 then
              if not(slstree.bins.ContainsKey(node.pathlen)) then
                 slstree.bins.Add(node.pathlen, List())
              slstree.bins.[node.pathlen].Add(nodeRef) |> ignore

           // set the pathlen of all children
           for c in node.children.Values do
              let child = GetNode slstree c
              child.pathlen <- child.end_i - child.beg_i + node.pathlen 

           // recurse on all children
           for c in node.children.Values do
              nodesToCheck.Push(c)
           
    /// Set the maximum beginning position, minimum beginning position, and number of 
    /// beginning positions of the nodes in the slstree 
    let SetMinMaxCard slstree = 
        for node in slstree.nodes do
           // leaf case
           if node.children.Count = 0 then
               node.num_beg_pos <- 1
               node.max_beg_pos <- node.end_i - node.pathlen
               node.min_beg_pos <- node.end_i - node.pathlen
           // lazily evaluate the internal node case later on

    /// Given an array of symbols, construct an SLS tree that indexes them
    let MKSLSTree (xs:Symbol []) = 
        let stree = MKSTree xs
        let tempNodes = Array.map (ToLNode stree) stree.nodes
        let slstree = { data = stree.data;
                        nodes = tempNodes;
                        bins = new Dictionary<int, List<int>>();} 
        setBins slstree 
        SetMinMaxCard slstree
        slstree
  
    let rec ContainsH tree (input:Symbol []) node = 
        if input = List.toArray [] then node 
        else
            let firstChar = input.[0]
            if node = 0 then
               if not(tree.nodes.[node].children.ContainsKey(firstChar)) then node
               else ContainsH tree input.[0..input.Length-1] tree.nodes.[node].children.[firstChar]
            else
               let compNode = tree.nodes.[node]
               let endIndex = compNode.end_i
               let compString = tree.data.[compNode.beg_i .. endIndex-1]
               if compString.Length >= input.Length then
                  if compString.[0 .. input.Length-1] = input then
                     node
                  else
                     -1
               else 
                  if (tree.nodes.[node].children.ContainsKey(input.[compString.Length]) && input.[0..compString.Length-1] = compString) then
                     ContainsH tree input.[compString.Length .. input.Length-1]  tree.nodes.[node].children.[input.[compString.Length]]
                  else
                     -1
                     
    /// Check if the tree indexes a particular string
    let Contains tree input =
        (ContainsH tree input 0) >= 0

    /// Update the minimum beginning position, maximum beginning position, and number of beginning positions
    /// from the children of the internal node. This is called lazily by the SLSTree rather than precomputed
    /// If any of the keys represent parts of the string that have already been replaced remove them
    let UpdateFromChildren slstree nodeRef = 
        let node = GetNode slstree nodeRef
        node.num_beg_pos <- 0
        node.min_beg_pos <- slstree.data.Length + 1
        node.max_beg_pos <- -1
        let deadKeys = new List<Symbol>()
        for k in node.children.Keys do
           let childRef = node.children.[k]
           let child = slstree.nodes.[childRef]
           // if this child is dead, remove it
           if child.beg_i = -3 then
              deadKeys.Add(k)
           else
               node.num_beg_pos <- node.num_beg_pos + child.num_beg_pos
               if node.min_beg_pos > child.min_beg_pos then
                  node.min_beg_pos <- child.min_beg_pos
               if node.max_beg_pos < child.max_beg_pos then
                  node.max_beg_pos <- child.max_beg_pos
        for k in deadKeys do
            node.children.Remove(k) |> ignore

    /// Replace all instances of the string indexed by nodeRef with the nonterminal symbol nonterm
    let ReplaceAllInstances slstree nodeRef nonterm endSymbol =
        let mutable replacedString = List.toArray [] 
        let node = GetNode slstree nodeRef

        // no positions of this node remaining
        if node.num_beg_pos = 0 then
            DeleteNode slstree nodeRef
        // if there is no replacement to be made, delete all of the children as the represent an arithmetic progression,
        // summarized by min, max, card
        elif node.max_beg_pos - node.min_beg_pos < node.pathlen then
            node.children.Clear()
        else
            // if there is a replacement to be made
            let mutable replaceList = new List<int>() 
            for cRef in node.children.Values do
                let child = GetNode slstree cRef
                // just one instance, not a sequence
                if child.num_beg_pos = 1 then
                    // this is the same as child.max_beg_pos
                    let replacePos = child.min_beg_pos
                    if not(IsDead slstree replacePos) && not(IsDead slstree (replacePos + node.pathlen-1)) then
                       replaceList.Add(replacePos) |> ignore
                // just two instances
                else if child.num_beg_pos = 2 then
                    if not(IsDead slstree child.min_beg_pos) && not(IsDead slstree (child.min_beg_pos + node.pathlen-1)) then
                      replaceList.Add(child.min_beg_pos) |> ignore
                    if child.min_beg_pos + node.pathlen <= child.max_beg_pos && not(IsDead slstree child.max_beg_pos) && not(IsDead slstree (child.max_beg_pos + node.pathlen-1)) then
                      replaceList.Add(child.max_beg_pos) |> ignore
                // the number of beginning positions to hop each time to find the next occurence to replace
                else
                    let d = (float child.max_beg_pos - float child.min_beg_pos)/(float child.num_beg_pos) |> ceil |> int
                    // some d may be dead because the previous d was a replace instance of the node string
                    let n = node.pathlen/d
                    for replacePos in [child.min_beg_pos .. n*d .. child.max_beg_pos] do 
                      if not(IsDead slstree replacePos) && not(IsDead slstree (replacePos + node.pathlen-1)) then
                         replaceList.Add(replacePos) |> ignore
            
            if replaceList.Count > 1 then
                DeleteNode slstree nodeRef
                replacedString <- slstree.data.[replaceList.[0] .. replaceList.[0] + node.pathlen-1]
                for replacePos in replaceList do
                    if not(IsDead slstree replacePos) && not(IsDead slstree (replacePos + node.pathlen-1)) then
                       MarkNonterm slstree replacePos (Nonterm nonterm)
                       MarkNothing slstree (replacePos+1) (node.pathlen-1) 
            elif replaceList.Count = 0 then
                DeleteNode slstree nodeRef
            else
                node.min_beg_pos <- replaceList.[0]
                node.max_beg_pos <- replaceList.[0]
                node.num_beg_pos <- 1
        replacedString

    /// Perform LFS on a string, assigning nonterminals with nontermStart and concatenating them in a string separated by endTermStart
    let LFSPass xs nontermStart endtermStart = 
        let slstree = MKSLSTree xs 
        let mutable len = xs.Length
        let mutable nonterm = nontermStart
        let mutable endSymbol = endtermStart 
        let mutable rules = new List<Symbol> ()
        while len > 1 do
            if slstree.bins.ContainsKey len then
                let bin = slstree.bins.[len]
                for nodeRef in bin do
                    let node = GetNode slstree nodeRef
                    UpdateFromChildren slstree nodeRef 
                    let replacedString = ReplaceAllInstances slstree nodeRef nonterm endSymbol
                    if replacedString.Length > 0 then
                       rules.AddRange(replacedString)
                       rules.Add(End endSymbol) 
                       nonterm <- nonterm + 1
                       endSymbol <- endSymbol + 1
                slstree.bins.Remove(len) |> ignore
            else
                len <- len - 1
        (slstree.data, rules.ToArray(), nonterm, endSymbol)

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
           // if no extra matching along the edge is found, check if one of the nodes has a child only 1 character away. If so, then there is a substitution from one of the leaves to
           // this edge character
           let mutable subSymbol = Nothing
           let mutable subNodeRef = -1
           for cRef in node.children.Values do
               let child = GetNode slstree cRef
               // edge length is only 1
               if not(IsLeaf slstree cRef) && child.end_i - child.beg_i = 1 then
                  subSymbol <- slstree.data.[child.beg_i] 
                  subNodeRef <- cRef
           // find a leaf to substitute from
           let mutable subLoc = -1
           for cRef in node.children.Values do
               if not(cRef = subNodeRef) && IsLeaf slstree cRef then
                  let child = GetNode slstree cRef
                  subLoc <- child.beg_i
           if not(subSymbol = Nothing) && subLoc >= 0 then
        //      (1, subLoc, subSymbol)
              (0, -1, Nothing)
           else
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