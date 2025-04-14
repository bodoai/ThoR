/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Formula.formula
import ThoR.Shared.Syntax.Formula.formulaService
import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.Syntax.AlloyData.alloyDataService

open Lean Lean.Elab Command Term
open Shared

namespace Alloy

  syntax
    (name := blockless_alloy)
    "[" ("#")? "alloy" "|"
      formula*
    "]"
    : term

  private def evalAlloyFormulaBlock
    (formulas : List Formula)
    (alloyDataList : List alloyData)
    (localContextUserNames : List Name)
    : Except String Term := do
      if formulas.isEmpty then
        return (unhygienicUnfolder `(term | True))
      else
        let mut formulas_typed := []
        for f in formulas do
          formulas_typed := formulas_typed.concat (← formula.toType f)

        let first_formula := formulas_typed.get! 0

        let mut result_term ← first_formula.toTermOutsideBlock alloyDataList localContextUserNames
        for formula in (formulas_typed.drop 1) do
          let formula_term ← formula.toTermOutsideBlock alloyDataList localContextUserNames
          result_term := unhygienicUnfolder `($result_term ∧ $formula_term)

        return result_term

  @[term_elab blockless_alloy]
  private def alloyFormulaBlockImpl : TermElab := fun stx expectedType? => do
    let environment ← getEnv
    let alloyDataState := getAlloyData environment

    -- only the data of created modules
    let alloyDataList :=
      (alloyDataState.toList.map fun ad => ad.2).filter fun ad => ad.isCreated

    let lctxUserNames :=
      (← getLCtx).decls.toList.foldl
      (fun result decl =>
        match decl with
          | Option.some declaration => result.concat declaration.userName
          | Option.none => result
      )
      []

    match stx with
      | `([ alloy | $formulas:formula* ]) =>
        let except_term_of_formulas :=
          evalAlloyFormulaBlock formulas.toList alloyDataList lctxUserNames

        match except_term_of_formulas with
          | Except.error msg =>
            logError msg
            elabTerm (← `(term | True)) expectedType?

          | Except.ok term_of_formulas =>
            elabTerm term_of_formulas expectedType?

      | `([ #alloy | $formulas:formula* ]) =>
        let except_term_of_formulas :=
          evalAlloyFormulaBlock formulas.toList alloyDataList lctxUserNames

        match except_term_of_formulas with
          | Except.error msg =>
            logError msg
            elabTerm (← `(term | True)) expectedType?

          | Except.ok term_of_formulas =>
            logInfo term_of_formulas.raw.prettyPrint
            elabTerm term_of_formulas expectedType?

      | _ => throwUnsupportedSyntax

end Alloy
