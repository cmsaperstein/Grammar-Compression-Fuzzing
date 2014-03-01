namespace STree
open System.Collections.Generic
open Grammar 

(*
	Comments and variable names are very similar to         
	http://stackoverflow.com/questions/9452701/ukkonens-suffix-tree-algorithm-in-plain-english

	However, the code is entirely original
*) 

type Node = {
    mutable beg_i : int
    mutable end_i : int 
    mutable s_link : int 
    mutable parent : int 
    mutable children : Dictionary<Symbol, int> 
    }

type STree = {
    data : Symbol [] 
    nodes : Node []
    }

type ActPoint = {
    mutable a_edge : int // necessary for when the current node is reassigned
    mutable a_length : int 
    mutable remainder : int
    mutable current_node : int
    mutable num_nodes : int
    mutable passed_over : int // keeps track of the characters finished so far
    mutable needs_link : int
    }

module Tree = 
    // prints the state of the insertion
    let printActPoint actPoint = 
        printf "a_length=%d \t" actPoint.a_length 
        printf "a_edge=%d \t" actPoint.a_edge
        printf "remainder=%d \t" actPoint.remainder
        printf "current_node=%d \t" actPoint.current_node 
        printf "passed_over=%d \t" actPoint.passed_over
        printf "needs_link=%d \t" actPoint.needs_link 

    let rec nodeToString tree node whitespace = 
        if node = 0 then
           printfn "%s" "."
        else if tree.nodes.[node].end_i < 0  then
           let endIndex = tree.nodes.Length - 1
           printfn "%s%d,%d" whitespace tree.nodes.[node].beg_i tree.nodes.[node].end_i
        else 
           printfn "%s%d,%d" whitespace  tree.nodes.[node].beg_i tree.nodes.[node].end_i
        for c in tree.nodes.[node].children.Keys do
           printfn "%s%A"  whitespace c
           nodeToString tree tree.nodes.[node].children.[c] (whitespace + "   ")

    let TreeToString tree = 
         nodeToString tree 0 ""

    let NodeEdge tree node = 
        let mutable endIndex = tree.nodes.[node].end_i
        let begIndex = tree.nodes.[node].beg_i
        if endIndex < 0 then endIndex <- tree.data.Length
        tree.data.[begIndex .. endIndex-1]

    // negative numbers represent unitialized values
    // insert a new blank node into the tree and return it's index
    let NewNode (tree:STree) (actPoint : ActPoint) = 
        let node = {
          beg_i = actPoint.a_edge + actPoint.a_length;
          end_i = -2;
          s_link = -2; 
          parent = -2;
          children = new Dictionary<Symbol, int>()}
        tree.nodes.[actPoint.num_nodes] <- node
        actPoint.num_nodes <- actPoint.num_nodes + 1
        actPoint.num_nodes - 1
    // Contains 1 root node and an array corresponding to an unfilled tree
    let DefaultNodes (length:int) =
        let defaultNode = {
            beg_i = -2;
            end_i = -2; 
            s_link = -2;
            parent = -2;
            children = new Dictionary<Symbol, int>()}
        Array.create length defaultNode 

    // Add a suffix link when a second internal node has been created 
    let UpdateSuffixLink tree actPoint node = 
        if actPoint.needs_link > 0 then
           tree.nodes.[actPoint.needs_link].s_link <- node
           //printf "\t%s" "adding a suffix link"
        actPoint.needs_link <- node 

    (*
	After an insertion from the root, 
	    active_node remains the root.
	    active_edge is set to the first character of the new suffix we need to insert.
	    active_length is reduced by 1

	After spplitting an edge from and active_node that is not the root, following the suffix link
	going out of that node, if there is any, and reset the active_node to the node it points to.
	If there is no suffix link, we set the active_node to the root. active_edge and active_length
	remain unchanged
    *)
    let FollowSuffixLink tree actPoint = 
        let nextNode = tree.nodes.[actPoint.current_node].s_link
        actPoint.remainder <- actPoint.remainder - 1
        actPoint.passed_over <- actPoint.passed_over + 1
        if actPoint.current_node = 0 then
           //printf "\t%s" "at root and staying there"
           if actPoint.a_length > 0 then
              actPoint.a_length <- actPoint.a_length - 1 
           actPoint.a_edge <- actPoint.passed_over 
        else if nextNode > 0 then
          // printf "\t%s" "folowing suffix link"
           actPoint.current_node <- nextNode
        else
           //printf "\t%s" "returning to root"
           actPoint.current_node <- 0
           actPoint.a_edge <- actPoint.passed_over 

    // Go along the active edge between the current node and the releveant child to determine if the current character is different at the insertion length.
    let NeedToSplitEdge c tree actPoint = 
        tree.nodes.[actPoint.current_node]
        |> fun child -> child.beg_i + actPoint.a_length - 1
        |> fun compIndex -> c = tree.data.[compIndex]

    // Check to see if it is possible to insert the active node at the current position. If so, do it. Otherwise, increment the active length and remainder
    let InsertAtCurrent c tree actPoint = 
        tree.nodes.[actPoint.current_node].children 
        |> (fun children ->
                match children.ContainsKey c with
                // whenever there is an insertion, decrement the remainder, and reset the current node to the root after following suffix links
                | false -> let n = NewNode tree actPoint
                           children.Add(c,n)
                           tree.nodes.[n].parent <- actPoint.current_node
                           FollowSuffixLink tree actPoint
                           //printf "\t%s" "inserted at current node"
                | true  -> // found child and continuing along the edge
                           actPoint.a_length <- actPoint.a_length + 1
                           actPoint.remainder <- actPoint.remainder + 1
                           actPoint.needs_link <- -1 
                           //printf "\t%s" "found child and going along edge"
        )
       
    // The situations Gusfield describes in his Suffix Tree construction algorithm 
    let rec AddChar tree actPoint = 
        let c = tree.data.[actPoint.a_edge + actPoint.a_length]
       // decide to either insert on the edge or at the current node        
        match actPoint.a_length with 
            | 0 -> InsertAtCurrent c tree actPoint
            | n -> 
                   let actChar = tree.data.[actPoint.a_edge]
                   let compNodeRef = tree.nodes.[actPoint.current_node].children.[actChar]
                   let compNode = tree.nodes.[tree.nodes.[actPoint.current_node].children.[actChar]]
                   // if the length is more than the current edge, set the current node to that and reset the acive_length
                   // don't increment the remainder because no charaacter comparision has been done
                   if compNode.end_i >=0 && actPoint.a_length >= (compNode.end_i - compNode.beg_i) then 
                        actPoint.current_node <- compNodeRef
                        actPoint.a_edge <- actPoint.a_edge + (compNode.end_i - compNode.beg_i) 
                        actPoint.a_length <- actPoint.a_length - (compNode.end_i - compNode.beg_i)
                        //printf "\t%s" "overtaking"
                   // if the edge is the same, continue walking down 
                   elif tree.data.[compNode.beg_i + n] = c then
                        actPoint.a_length <- actPoint.a_length + 1
                        actPoint.remainder <- actPoint.remainder + 1
                        actPoint.needs_link <- -1
                        //printf "\t%s: char=%c" "walking down" c
                   // otherwise, break the edge and add a two new nodes at the break point 
                   else
                        //printf "\t%s" "splitting the node"
                        // Edge from i to j is broken at element k
                        let i = compNode.beg_i
                        let j = compNode.end_i
                        let k = actPoint.a_length + i
                        let breakPointP = NewNode tree actPoint
                        let breakPointC = NewNode tree actPoint
                        compNode.beg_i <- k
                        compNode.end_i <- j
                        if tree.nodes.[actPoint.current_node].children.ContainsKey(tree.data.[i]) then
                           ignore(tree.nodes.[actPoint.current_node].children.Remove(tree.data.[i]))
                        tree.nodes.[actPoint.current_node].children.Add(tree.data.[i], breakPointP)
                        tree.nodes.[breakPointP].parent <- actPoint.current_node
                        tree.nodes.[breakPointP].children.Add(c, breakPointC)
                        tree.nodes.[breakPointC].parent <- breakPointP
                        tree.nodes.[breakPointP].children.Add(tree.data.[compNode.beg_i], compNodeRef)
                        tree.nodes.[compNodeRef].parent <- breakPointP
                        tree.nodes.[breakPointP].beg_i <- i
                        tree.nodes.[breakPointP].end_i <- k

                        UpdateSuffixLink tree actPoint breakPointP
                        FollowSuffixLink tree actPoint

    let MKSTree(input: Symbol [] ) = 
        let tree = {data = input; nodes = DefaultNodes (input.Length*2 + 2)}
        let actPoint  = {a_edge = 0; a_length = 0; remainder = 0; current_node=0; num_nodes=0; passed_over = 0; needs_link = -1}
        // create the root
        // passed_over is the number of characters that have been passed over
        NewNode tree actPoint |> ignore
        while actPoint.passed_over <= tree.data.Length do
            if actPoint.remainder = 0 then
               actPoint.remainder <- 1
               actPoint.needs_link <- -1
               actPoint.a_length <- 0
               actPoint.a_edge <- actPoint.passed_over
            // indicate that something more needs to be inserted
            // if we are on the last substriing to insert and it has already occured in the tree, keep incrementing 
            if actPoint.a_edge + actPoint.a_length < tree.data.Length then
                //printf "current=%c \t" tree.data.[actPoint.a_edge] 
                //printActPoint actPoint
                AddChar tree actPoint
            else
                //printActPoint actPoint
                actPoint.passed_over <- tree.data.Length + 1
            //printfn "%s" ""
        // post processing step: replace all -2 end indices with the lengh of the input 
        for i in 0..tree.nodes.Length-1 do
            if tree.nodes.[i].end_i < 0 then
               tree.nodes.[i].end_i <- tree.data.Length
        tree

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

    let Contains tree input =
        (ContainsH tree input 0) >= 0

    let FindNode tree input =
        ContainsH tree input 0