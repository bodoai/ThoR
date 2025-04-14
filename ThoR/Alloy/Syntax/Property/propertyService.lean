/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Property.property
import ThoR.Shared.Syntax.Formula.formulaService

open Shared
open Lean

namespace Alloy.property

  /-- Creates a property from a name and formulas -/
  private def create
    (name : Name)
    (formulas : TSyntaxArray `formula)
    (signatureName : String := "")
    (signatureRelationNames : List String := [])
    : Except String property := do

    let mut formulas_typed := []
    for f in formulas do
      formulas_typed :=
        formulas_typed.concat (← formula.toType f signatureRelationNames)

    if !(signatureName.isEmpty) &&
        !(signatureRelationNames.isEmpty) &&
          !(formulas.isEmpty) then

      return {
        name:= name.toString,
        formulas := [
          formula.quantification
            (quantifier := quant.all)
            (disjunction := false)
            (names := ["this"])
            (typeExpression :=
              typeExpr.relExpr (expr.string (signatureName)))
            (formulas := formulas_typed)
        ]
      }
    else
      return {
        name:= name.toString,
        formulas := formulas_typed
      }

  /-- Creates a type representation from syntax and a name-/
  def toType
    (name: Name)
    (p : Property)
    (signatureName : String := "")
    (signatureRelationNames : List String := [])
    : Except String property :=
    match p with
      | `(property | { $formulas:formula*}) =>
        return ← create name formulas signatureName signatureRelationNames
      | syntx =>
          throw s!"No match implemented in \
          propertyService.toType \
          for '{syntx}'"

end Alloy.property
