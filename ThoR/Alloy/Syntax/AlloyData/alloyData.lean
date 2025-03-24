/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Alloy.Syntax.AST.AST
import ThoR.Alloy.SymbolTable

open ThoR Shared Alloy
open Lean Lean.Elab Command Term

/-
All needed Data to create Alloy Commands
-/
namespace Alloy

  structure alloyData where
    (ast : AST)
    (st : SymbolTable)

  namespace alloyData

    instance : ToString alloyData where
      toString ( ad : alloyData ) : String :=
        s!"AlloyData : \{
            abstract syntax tree := {ad.ast},
            symbol table := {ad.st}
          }"

    instance : Inhabited alloyData where
      default := {ast := default, st := default}

  end alloyData

  abbrev alloyDataState := NameMap alloyData

end Alloy
