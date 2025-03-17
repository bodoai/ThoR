/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Function.FunctionIfDecl.functionIfDecl
import ThoR.Shared.Syntax.Formula.formulaService
import ThoR.Alloy.UnhygienicUnfolder

open Lean
open Shared

namespace Alloy.functionIfDecl

  def toTerm
    (fid : functionIfDecl)
    (blockName : Name)
    (variableNames : List (String))
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    : Except String Term := do
      let conditionTerm ← fid.condition.toTerm blockName variableNames callableVariables callablePredicates
      let thenBodyTerm := fid.thenBody.toTermFromBlock blockName

      let mut term : Unhygienic Term :=
        `($(conditionTerm) → $(thenBodyTerm))

      if fid.hasElse then
        let elseBodyTerm := fid.elseBody.toTermFromBlock blockName
        term :=
          `(term |
            ($(unhygienicUnfolder term)) ∧
            (Not $(conditionTerm) → $(elseBodyTerm))
          )

      return unhygienicUnfolder term

  partial def toType (fid : FunctionIfDecl) : functionIfDecl :=
    match fid with
      | `(functionIfDecl |
        ( $fid:functionIfDecl )) => toType fid

      | `(functionIfDecl |
        /-
        since the if condition in formula has the same syntax
        there the matching is a bit convoluted...
        -/
        $condition:formula $h:fidHack) =>
          match h with
            | `(fidHack| => $thenBody:expr) =>
              functionIfDecl.mk
                (condition := formula.toType condition)
                (thenBody := expr.toType thenBody)
                (elseBody := default)
                (hasElse := false)

            | `(fidHack| => $thenBody:expr else $elseBody:expr) =>
              functionIfDecl.mk
                (condition := formula.toType condition)
                (thenBody := expr.toType thenBody)
                (elseBody := expr.toType elseBody)
                (hasElse := true)

            | _ => unreachable!

      | _ => unreachable!

end Alloy.functionIfDecl
