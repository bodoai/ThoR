/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Relation.ElabCallMacro
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.Syntax.AlloyData.alloyDataService
import Lean

open Alloy
open Lean Lean.Elab Tactic

/--
Declares a new fact with the given name, refering to one created from
an alloy block.

Defined like "fact `new_name` : `refered_name`"
-/
syntax (name:= fact_declaration) "fact" ident ":" ident : tactic

@[tactic fact_declaration]
private def factDeclaraionImpl : Tactic := fun stx => do
  let environment ← getEnv
  let alloyDataState := getAlloyData environment
  let alloyDataList :=
    (alloyDataState.toList.map fun ad => ad.2).filter fun ad => ad.isCreated

  match stx with
    | `(tactic | fact $new_name : $refered_name) =>
      let mut possibleFacts := []
      for alloyData in alloyDataList do
        let possibleMatches :=
          (alloyData.st.axiomDecls).filter
            fun cd => cd.name == refered_name.getId.toString

        if !possibleMatches.isEmpty then
          possibleFacts := possibleFacts.concat
            (alloyData.st.name, possibleMatches)

      if !possibleFacts.isEmpty then
        if
          -- if there are matches in more than one module
          possibleFacts.length > 1 ||
          -- or more than one match in a module (this should be impossible)
          possibleFacts.any fun pv => pv.2.length > 1
        then
          logError s!"The call to {refered_name} is ambiguous. \
          There are multiple declared definitions which it could refer to ({possibleFacts})"

        let declsOfBlock := possibleFacts.get! 0
        let calledBlockName := declsOfBlock.1

        let refName := refered_name.getId

        let calledNameComponents :=
          calledBlockName.components ++ [`facts, refName]

        let calledName : Name := Name.fromComponents calledNameComponents

        evalTactic (← `(tactic | have $new_name := ∻ $(mkIdent calledName)))
        return

      evalTactic (← `(tactic | have $new_name := ∻ $refered_name))


    | _ => unreachable!
