namespace Demo

open System.IO
open Grammar
open Grammar.Utils
open SLSTree.Tree
open LFS.LFS
open Fuzzing.Fuzzing
open FsCheck

module Demo  = 
    let fileName = "C:\\Users\\Craig\\Desktop\\message.txt" 

    let runDemo() = 
        File.ReadAllText fileName
        |> fun contents -> seq {for lfsFun, lfsName in [(LFS3, "LSF3"); (LFS2, "LSF2"); (LFS1, "LSF1")] -> (contents |> lfsFun |> RulesPairToString, lfsName)}
        |> Seq.map (fun (compressed, lfsName) -> 
               let i = new StreamWriter (fileName + "-" + lfsName)
               i.Write(compressed)
               i.Close())