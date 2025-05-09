/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Function.FunctionIfDecl.functionIfDecl
import ThoR.Shared.Syntax.Formula.formulaService
import ThoR.Alloy.UnhygienicUnfolder

import ThoR.Alloy.Exceptions.NoMatchImplementedException

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

      let elseBodyTerm ← fid.elseBody.toTermFromBlock blockName
      term :=
        `(term |
          ($(unhygienicUnfolder term)) ∧
          (Not $(conditionTerm) → $(elseBodyTerm))
        )

      return unhygienicUnfolder term

  partial def toType
    (fid : FunctionIfDecl)
    : Except String functionIfDecl :=
      match fid with
        | `(functionIfDecl |
          ( $fid:functionIfDecl )) => toType fid

        | `(functionIfDecl |
          $condition:formula_without_if $_:connector $thenBody:expr else $elseBody:expr) =>
          return functionIfDecl.mk
            (condition := ← formula.toType_withoutIf condition)
            (thenBody := ← expr.toType thenBody)
            (elseBody := ← expr.toType elseBody)

        | `(functionIfDecl |
          ( $condition:formula ) $_:connector $thenBody:expr else $elseBody:expr) =>
          return functionIfDecl.mk
            (condition := ← formula.toType condition)
            (thenBody := ← expr.toType thenBody)
            (elseBody := ← expr.toType elseBody)

        | syntx =>
          throwNoMatchImplemented "functionIfDeclService.toType" syntx

end Alloy.functionIfDecl
