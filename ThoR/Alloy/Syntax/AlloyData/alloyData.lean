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
    (isCreated : Bool := false)
  deriving Inhabited

  namespace alloyData

    instance : ToString alloyData where
      toString ( ad : alloyData ) : String :=
        s!"AlloyData : \{
            abstract syntax tree := {ad.ast},
            symbol table := {ad.st},
            isCreated := {ad.isCreated}
          }"

  end alloyData

  abbrev alloyDataState := NameMap alloyData

end Alloy
