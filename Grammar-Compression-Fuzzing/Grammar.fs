namespace Grammar 

///   <summary> Represents the kinds of characters that can appear in the output
///   </summary>
///   <param name = "Term"> Terminal in a grammar. Base character of the input </param>
///   <param name = "Nonterm"> A nonterminal in a grammar </param>
///   <param name = "End"> A unique separator character that only appears once </param>
///   <param name = "Nothing"> Empty space, characters that have been substituted by a grammar rule </param>
type Symbol = 
   | Term of char
   | Nonterm of int
   | End of int
   | Nothing

///   <summary> Represents a grammar rule, where lhs is the symbol, and rhs is the subsitution rule
///    A -> aBc    
///
///    lhs = A
///    rhs = aBc
///   </summary>
///   <param name = "lhs"> Left side of grammar rule. Only 1 nonterminal</param>
///   <param name = "rhs"> Right side of grammar rule. Combinatino of terminals and nonterminals</param>
type Rule = {
    lhs : Symbol 
    rhs : Symbol [] 
    }

module Utils = 
    /// Translate a string into an array of symbols
    let LiftSymbol (xs:string) = 
        let xsSymbol = Array.zeroCreate xs.Length 
        for i in [0..xsSymbol.Length-1] do
            xsSymbol.[i] <- Term xs.[i] 
        xsSymbol

    /// Translate a symbol array into a string
    let convToString (xs: Symbol []) = 
       let sb = new System.Text.StringBuilder()
       for s in xs do
           match s with 
           | Term c -> sb.Append(c) |> ignore
           | _ -> ()
       sb.ToString()

    /// Counts the numer of non-nothing symbols
    let CountAlive (symbols:Symbol []) = 
        let mutable count = 0
        for s in symbols do
            match s with
            | Nothing -> ()
            | End _ -> ()
            | _ -> count <- count + 1
        count

    /// Count number of nothing symbols
    let CountDead (xs:Symbol []) = 
        let mutable count = 0
        for s in xs do
            match s with
            | Nothing -> count <- count+1 
            | _ -> ()
        count

    /// Count number of ending symbols
    let CountEnd (xs:Symbol []) = 
        let mutable count = 0
        for s in xs do
            match s with
            | End _ -> count <- count+1 
            | _ -> ()
        count

    /// Count number of terminal symbols
    let CountTerm (xs:Symbol []) = 
        let mutable count = 0
        for s in xs do
            match s with
            | Term _ -> count <- count+1 
            | _ -> ()
        count

    let GrammarSize (baseRule:Symbol[], otherRules:Symbol[]) =  
        CountAlive baseRule + CountAlive otherRules 

    /// Take a symbol array and return another without any "nothing symbols"
    let RemoveNothings (xs: Symbol[]) = 
        let newLength = xs.Length - CountDead xs
        let newXS = Array.create newLength Nothing 
        let mutable i = 0
        for sym in xs do
            match sym with 
            | Nothing -> ()
            | _ -> newXS.[i] <- sym
                   i <- i+1
        newXS

    /// Tell if the character is a terminal character
    let IsTerm (x:Symbol) = 
        match x with 
        | Term _ -> true
        | _ -> false

    /// Find the index of this end symbol
    let FindEndIndex (xs:Symbol[]) endNum =
        let mutable endLocation = 0
        for i in [0 .. xs.Length-1] do
            if xs.[i] = (End endNum) then
                endLocation <- i
        endLocation
    
    /// Given a Term Character, Convert to a Char 
    let SymToChar (x:Symbol) = 
        match x with 
        | Term c -> c
        | _ -> ' ' 