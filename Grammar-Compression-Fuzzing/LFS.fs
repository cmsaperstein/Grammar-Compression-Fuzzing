namespace LFS 
open System.Collections.Generic
open System.Collections 
open Grammar
open Grammar.Utils
open SLSTree.Tree

open System.IO

module LFS = 
    /// Gives the ratio of the number of non-dead output symbols to non-dead input symbols
    let CompressionRatio baseRule otherRules = 
        let outputSize = CountAlive baseRule + CountAlive otherRules
        let inputSize = baseRule.Length - 1
        (float outputSize) / (float inputSize)

    /// Translates the array for of grammar rules, where each rule is divided with an <End i> character to a hashmap of rules
    let RulesToHashMap (rules:Symbol []) = 
        let rulesHash = new Dictionary<Symbol, Symbol []>()
        let mutable ruleStart = 0
        let mutable ruleEnd = 0
        while ruleEnd < rules.Length do
            match rules.[ruleEnd] with
            |   End n -> rulesHash.Add(Nonterm n, RemoveNothings rules.[ruleStart .. ruleEnd-1])
                         ruleStart <- ruleEnd + 1
                         ruleEnd <- ruleEnd + 1
            |   _ -> ruleEnd <- ruleEnd + 1
        rulesHash

    /// Given the rules hash map, find the base rule, and substitute in grammar rules until the uncompressed input is found
    let DecompressRulesHashMap (rules:Dictionary<Symbol, Symbol[]>) =
        let mutable maxNonterm = 0
        // work from last rule to avoid non-constant stack depth
        for nonterm in rules.Keys do 
            match nonterm with 
            | Nonterm i -> if i > maxNonterm then maxNonterm <- i
            | _ -> ()

        while maxNonterm > 0 do
            let currentRule = rules.[Nonterm maxNonterm] 
            let mutable newRule = new List<Symbol>()
            for sym in currentRule do
                match sym with
                | Term s -> newRule.Add(sym)
                | Nonterm x -> newRule.AddRange(rules.[Nonterm x])
                | End i -> printfn  "unwanted end character:%d" i
                | Nothing -> ()
            rules.Remove(Nonterm maxNonterm) |> ignore
            rules.Add(Nonterm maxNonterm, newRule.ToArray())
            maxNonterm <- maxNonterm - 1

    // handles cases where there are rules of the form A -> B, where B is a single nonterminal 
    let RemoveRedundancy (lfsBase:Symbol[]) (lfs2OtherRules:Symbol []) =
       let ruleHash = RulesToHashMap lfs2OtherRules
       // k,v is a member, implies that all instances of k should be replaced with v
       let nontermReplacements = new Dictionary<Symbol, Symbol> ()
       // k is a member implies that ruleHash.[k] should be removed
       let nontermDeletions = new HashSet<int>()
       for lhs in ruleHash.Keys do 
           let rhs = ruleHash.[lhs]
           if rhs.Length = 1 then
              match rhs.[0] with 
              | Nonterm x -> nontermReplacements.Add(lhs, rhs.[0])
                             match lhs with 
                             | Nonterm y -> nontermDeletions.Add(y) |> ignore
                             | _ -> printfn "left side of rule should be a nonterm: for some reason it isnt"
              | _ -> printf "rule has only 1 elemnt on rhs: this shouldn't happend"
       // perform replacements in the base rule
       for i in [0 .. lfsBase.Length-1] do
           if nontermReplacements.ContainsKey(lfsBase.[i]) then
              lfsBase.[i] <- nontermReplacements.[lfsBase.[i]]

       // delete singletons in the other rules
       let mutable i = lfs2OtherRules.Length - 1
       let mutable deleting = false
       while i > 0 do 
           match lfs2OtherRules.[i] with
           | End x ->  
                if nontermDeletions.Contains(x) then
                   deleting <- true
                   lfs2OtherRules.[i] <- Nothing
                else
                   deleting <- false
           | _ -> if deleting then 
                     lfs2OtherRules.[i] <- Nothing
           i <- i-1
       (lfsBase, lfs2OtherRules) 

    /// Take some rules and transform it into a grammar
    let RulesToString baseRule otherRules =  
        let mutable baseRuleSB = new System.Text.StringBuilder() 
        for s in baseRule do
            match s with 
            | Nothing -> () 
            | End x -> baseRuleSB.Append(" $_{" + (string x) + "}") |> ignore
            | Nonterm x -> baseRuleSB.Append("A_{" + string x + "}") |> ignore
            | Term x -> baseRuleSB.Append(string x) |> ignore

        let mutable otherRulesSB = new System.Text.StringBuilder()
        let mutable currentRule = new System.Text.StringBuilder()
        for s in otherRules do
            match s with 
            | Nothing -> () 
            | End x -> otherRulesSB.Append("A_{"+string x+"} -> ")
                                   .Append(currentRule.ToString() + "\n") |> ignore
                       if currentRule.Length < 2 then
                          printfn "error: rule has length less than 2"
                       currentRule <- new System.Text.StringBuilder()
            | Nonterm x -> currentRule.Append("A_{" + string x + "}") |> ignore
            | Term x -> currentRule.Append(string x) |> ignore
        
        baseRuleSB.ToString() + "\n\n" + otherRulesSB.ToString()

    let RulesPairToString (baseRule, otherRules) = 
        RulesToString baseRule otherRules

    let OutputRules baseRule otherRules = 
        let outString = RulesToString baseRule otherRules
        let wr = new StreamWriter("C:\\Users\\Craig\\Desktop\\outputgrammar.txt", false)
        wr.Write(outString)
        wr.Close()

    let OutputOriginal (s:string)  = 
        let outString = s 
        let wr = new StreamWriter("C:\\Users\\Craig\\Desktop\\original.txt", false)
        wr.Write(outString)
        wr.Close()

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


    /// Run LFS1 on the input
    let LFS1 (xs:string) = 
        let xSymbols = Array.append (LiftSymbol xs) (List.toArray [End 0])
        let (lfsBase, lfsRules, nonterm1, end1) = LFSPass xSymbols 1 1
        OutputRules lfsBase lfsRules 
        (lfsBase, lfsRules)

    /// Run LFS2  on the input
    /// Rules found later on in LFS1 are used on the RHS in previous rules
    let LFS2 (xs:string) = 
        let xSymbols = Array.append (LiftSymbol xs) (List.toArray [End 0])
        let (lfsBase, lfsOtherRules, nonterm1, end1) = LFSPass xSymbols 1 1
        let (lfsRulesSubstituted, subsToGetToLFS2, _, _) = LFSPass lfsOtherRules nonterm1 end1
        let lfs2Rules = Array.append lfsRulesSubstituted subsToGetToLFS2
        let (lfs2Base, lfs2OtherRules) = RemoveRedundancy lfsBase lfs2Rules
        OutputRules lfs2Base lfs2OtherRules 
        (lfs2Base, lfs2OtherRules)
    
    /// Run LFS2 on the input
    /// LFS2 + rules are added for redundancy between the lfs1 grammar and the base rule
    let LFS3(xs:string) =
        let xSymbols = Array.append (LiftSymbol xs) (List.toArray [End 0])
        let (lfs1Base, lfs1OtherRules, nonterm1, end1) = LFSPass xSymbols 1 1
        let (lfsRulesSubstituted, subsToGetToLFS3, _, _) = LFSPass (Array.append lfs1Base lfs1OtherRules) nonterm1 end1
        let lfs3BaseBeforeReduction = lfsRulesSubstituted.[0 .. lfs1Base.Length-1]
        let lfs3Rules = Array.append lfsRulesSubstituted subsToGetToLFS3
        let (lfs3Base, lfs3RulesWithBase) = RemoveRedundancy lfs3BaseBeforeReduction lfs3Rules
        let lfs3OtherRules = lfs3RulesWithBase.[ FindEndIndex lfs3RulesWithBase 0 + 1.. lfs3RulesWithBase.Length-1]
        OutputRules lfs3Base lfs3OtherRules
        OutputOriginal xs
        (lfs3Base, lfs3OtherRules)

    /// Given a grammar, output the plaintext that this grammar corresponds to.
    let Decompress (lfsBase,lfsRules) = 
        let mutable ruleHash = RulesToHashMap lfsRules 
        DecompressRulesHashMap ruleHash
        let decompressedBase = new List<Symbol>()
        for sym in lfsBase do
            match sym with 
            | Term s -> decompressedBase.Add(Term s)
            | Nonterm i -> decompressedBase.AddRange(ruleHash.[Nonterm i])
            | _ -> ()
        decompressedBase.ToArray() |> convToString
    
   
 



