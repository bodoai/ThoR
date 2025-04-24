/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Formula.formula
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl
import ThoR.Alloy.Syntax.Predicate.PredDecl.predDecl

import ThoR.Shared.Syntax.Relation.Expr.exprService
import ThoR.Shared.Syntax.TypeExpr.typeExprService
import ThoR.Shared.Syntax.Algebra.AlgExpr.algExprService
import ThoR.Shared.Syntax.Mutuals.mutualsService

import ThoR.Relation.Elab
import ThoR.Relation.SubType
import ThoR.Relation.Quantification
import ThoR.Alloy.Config

import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.UnhygienicUnfolder

open Alloy ThoR ThoR.Quantification
open Lean ThoR Config

namespace Shared.formula

  partial def toType_withoutIf
    (f : Formula_without_if)
    (signatureFactSigNames : List String := [])
    : Except String formula := do
      match f with
        | `(formula_without_if| ( $fwi:formula_without_if )) =>
          return ← toType_withoutIf fwi

        | `(formula_without_if| $name:ident) =>
          return formula.string name.getId.toString

        | `(formula_without_if| $predName:ident [$predargs,*]) =>
          let mut arguments_typed := []
          for argument in predargs.getElems do
            arguments_typed := arguments_typed.concat
              (← expr.toType argument signatureFactSigNames)

          return formula.pred_with_args
            predName.getId.toString
            arguments_typed

        | `(formula_without_if| $op:unRelBoolOp $expression:expr ) =>
          return formula.unaryRelBoolOperation
            (← unRelBoolOp.toType op) (← expr.toType expression signatureFactSigNames)

        | `(formula_without_if| $op:unLogOp $f:formula_without_if ) =>
          return formula.unaryLogicOperation
            (← unLogOp.toType op) (← toType_withoutIf f)

        | `(formula_without_if| $form1:formula_without_if $op:binLogOp $form2:formula_without_if) =>
          return formula.binaryLogicOperation
            (← binLogOp.toType op) (← toType_withoutIf form1) (← toType_withoutIf form2)

        | `(formula_without_if|
            $algExpr1:algExpr
            $compOp:algCompareOp
            $algExpr2:algExpr) =>
          return formula.algebraicComparisonOperation
            (← algCompareOp.toType compOp)
            (← algExpr.toType algExpr1)
            (← algExpr.toType algExpr2)

        | `(formula_without_if|
            $expr1:expr
            $op:relCompareOp
            $expr2:expr) =>
          return formula.relationComarisonOperation
            (← relCompareOp.toType op)
            (← expr.toType expr1 signatureFactSigNames)
            (← expr.toType expr2 signatureFactSigNames)

        | `(formula_without_if|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula_without_if
            ) =>
          return formula.quantification
            (← quant.toType q)
            true
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            ([← toType_withoutIf form])

        | `(formula_without_if|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            { $form:formula_without_if* }
            ) =>

          let mut forms_typed := []
          for f in form do
            forms_typed := forms_typed.concat (← toType_withoutIf f)

          return formula.quantification
            (← quant.toType q)
            true
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            forms_typed

        | `(formula_without_if|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula_without_if
            ) =>
          return formula.quantification
            (← quant.toType q)
            false
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            ([← toType_withoutIf form])

        | `(formula_without_if|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            {$form:formula_without_if*}
            ) =>
          let mut forms_typed := []
          for f in form do
            forms_typed := forms_typed.concat (← toType_withoutIf f)
          return formula.quantification
            (← quant.toType q)
            false
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            forms_typed

        -- let declaration
        | `(formula_without_if | $alloy_let_decl:alloyLetDecl) =>
          match alloy_let_decl with
            | `(alloyLetDecl | let $name:ident = $value:formula_without_if | $body:formula_without_if) =>
              return formula.letDeclaration
                (name := name.getId)
                (value := ← formula.toType_withoutIf value)
                (body := [← formula.toType_withoutIf body])
            | `(alloyLetDecl |
                let $name:ident = $value:formula_without_if |
                { $body:formula_without_if* }
              ) =>

              let mut body_typed := []
              for f in body do
                body_typed := body_typed.concat (← formula.toType_withoutIf f)

              return formula.letDeclaration
                (name := name.getId)
                (value := ←formula.toType_withoutIf value)
                (body := body_typed)
            | syntx => throw s!"No match implemented in \
              formulaSerivce.toType (let match) \
              for '{syntx}'"

        | syntx => throw s!"No match implemented in \
              formulaSerivce.toType \
              for '{syntx}'"

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (f : Formula)
    (signatureFactSigNames : List String := [])
    : Except String formula := do
      match f with
        | `(formula| $fwi:formula_without_if) =>
          return ← toType_withoutIf fwi signatureFactSigNames
        | `(formula| $form1:formula _:formula_if_connector $form2:formula else $form3:formula) =>
          return formula.tertiaryLogicOperation terLogOp.ifelse
              (← toType form1) (← toType form2) (← toType form3)

        | syntx => throw s!"No match implemented in \
            formulaService.toType \
            for '{syntx}'"

end Shared.formula
