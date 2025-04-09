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
    (pureNames : List (String) := [])
    : Except String Term := do
      let conditionTerm ← fid.condition.toTerm blockName variableNames callableVariables callablePredicates pureNames
      let thenBodyTerm ← fid.thenBody.toTermFromBlock blockName pureNames

      let mut term : Unhygienic Term :=
        `($(conditionTerm) -> $(thenBodyTerm))

      if fid.hasElse then
        let elseBodyTerm ← fid.elseBody.toTermFromBlock blockName pureNames
        term :=
          `(term |
            ($(unhygienicUnfolder term)) ∧
            (Not $(conditionTerm) -> $(elseBodyTerm))
          )

      return unhygienicUnfolder term

  partial def toType (fid : FunctionIfDecl) : functionIfDecl :=
    match fid with
      | `(functionIfDecl |
        ( $fid:functionIfDecl )) => toType fid

      | `(functionIfDecl |
        $condition:formula_without_if $_:connector $thenBody:expr) =>
        functionIfDecl.mk
          (condition := formula.toType_withoutIf condition)
          (thenBody := expr.toType thenBody)
          (elseBody := default)
          (hasElse := false)

      | `(functionIfDecl |
        ( $condition:formula ) $_:connector $thenBody:expr) =>
        functionIfDecl.mk
          (condition := formula.toType condition)
          (thenBody := expr.toType thenBody)
          (elseBody := default)
          (hasElse := false)

      | `(functionIfDecl |
        $condition:formula_without_if $_:connector $thenBody:expr else $elseBody:expr) =>
        functionIfDecl.mk
          (condition := formula.toType_withoutIf condition)
          (thenBody := expr.toType thenBody)
          (elseBody := expr.toType elseBody)
          (hasElse := true)

      | `(functionIfDecl |
        ( $condition:formula ) $_:connector $thenBody:expr else $elseBody:expr) =>
        functionIfDecl.mk
          (condition := formula.toType condition)
          (thenBody := expr.toType thenBody)
          (elseBody := expr.toType elseBody)
          (hasElse := true)

      | _ => default

end Alloy.functionIfDecl
