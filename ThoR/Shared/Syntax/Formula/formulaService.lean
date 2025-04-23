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

  /--
  Returns the required definitions for the formula to work in Lean
  -/
  partial def getReqDefinitions
    (f : formula)
    : List (String) := Id.run do
      match f with
        | formula.string s => [s]
        | formula.pred_with_args p _ => [p]
        | formula.unaryRelBoolOperation _ _ => []
        | formula.unaryLogicOperation _ f => f.getReqDefinitions
        | formula.binaryLogicOperation _ f1 f2 =>
          f1.getReqDefinitions.append f2.getReqDefinitions
        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          (f1.getReqDefinitions.append f2.getReqDefinitions).append f3.getReqDefinitions
        | formula.algebraicComparisonOperation _ _ _ => []
        | formula.relationComarisonOperation _ _ _ => []
        | formula.quantification _ _ n _ f =>
          ((f.map fun form =>
            form.getReqDefinitions).join
              ).filter fun (elem) => !(n.contains elem)
        | formula.letDeclaration _ value body =>
          let value_rd := value.getReqDefinitions
          let body_rds := (body.map fun e => e.getReqDefinitions).join
          body_rds ++ value_rd

  /--
  Gets all calls to the `callablePredicates`

  The result takes the form of a List of Tuples which contain called Predicates
  (as commandDecl) with the given arguments (as varDecl)
  -/
  partial def getCalledPredicates
    (f : formula)
    (callablePredicates : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      let callablePredicateNames := callablePredicates.map fun cp => cp.name

      match f with
        | formula.string s =>
          if callablePredicateNames.contains s then
            let index := callablePredicateNames.indexOf s
            let calledPredicate := callablePredicates.get! index
            return [(calledPredicate, [])]
          else
            return []

        | formula.pred_with_args predicate_name predicate_arguments =>
          if callablePredicateNames.contains predicate_name then
            let index := callablePredicateNames.indexOf predicate_name
            let calledPredicate := callablePredicates.get! index

            let mut calledArgumentVariables := []
            for arg in predicate_arguments do
              calledArgumentVariables :=
                calledArgumentVariables.concat
                  (arg, (← arg.getCalledVariables callableVariables))

            return [(calledPredicate, calledArgumentVariables)]
          else
            return []

        | formula.unaryLogicOperation _ f =>
          f.getCalledPredicates callablePredicates callableVariables

        | formula.binaryLogicOperation _ f1 f2 =>
          let f1_calls ← (f1.getCalledPredicates callablePredicates callableVariables)
          let f2_calls ← (f2.getCalledPredicates callablePredicates callableVariables)
          return f1_calls ++ f2_calls

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          let f1_calls ← (f1.getCalledPredicates callablePredicates callableVariables)
          let f2_calls ← (f2.getCalledPredicates callablePredicates callableVariables)
          let f3_calls ← (f3.getCalledPredicates callablePredicates callableVariables)
          return f1_calls ++ f2_calls ++ f3_calls

        | formula.quantification _ _ _ _ f =>
          let mut result := []
          for form in f do
            result := result ++ (← form.getCalledPredicates callablePredicates callableVariables)
          return result

        | formula.letDeclaration _ value body =>
          let value_cp ← value.getCalledPredicates callablePredicates callableVariables
          let mut body_cps := []
          for element in body do
            let calledPreds ← element.getCalledPredicates callablePredicates callableVariables
            body_cps := body_cps ++ calledPreds
          return body_cps ++ value_cp

        | _ => return []

  partial def insertModuleVariables
    (f : formula)
    (moduleVariables openVariables : List (String))
    : formula :=
    match f with
      | formula.pred_with_args p args =>
        pred_with_args
          p
          (args.map fun arg =>
            arg.insertModuleVariables moduleVariables openVariables)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation
          op
          (e.insertModuleVariables moduleVariables openVariables)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation
          op
          (f.insertModuleVariables moduleVariables openVariables)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.insertModuleVariables moduleVariables openVariables)
          (f2.insertModuleVariables moduleVariables openVariables)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
        op
        (f1.insertModuleVariables moduleVariables openVariables)
        (f2.insertModuleVariables moduleVariables openVariables)
        (f3.insertModuleVariables moduleVariables openVariables)
      | formula.quantification q d n t f =>
        formula.quantification
        q
        d
        n
        (t.insertModuleVariables moduleVariables openVariables)
        (f.map fun f =>
          f.insertModuleVariables moduleVariables openVariables)

      | formula.letDeclaration name value body =>
        formula.letDeclaration
          (name)
          (value.insertModuleVariables moduleVariables openVariables)
          (body.map fun f => f.insertModuleVariables moduleVariables openVariables)

      | _ => f

end Shared.formula
