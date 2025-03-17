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

import ThoR.Relation.Elab
import ThoR.Relation.SubType
import ThoR.Relation.Quantification

open Alloy ThoR ThoR.Quantification
open Lean ThoR

namespace Shared.formula

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given formula `f`
  -/
  partial def replaceCalls
    (f: formula)
    (callables : List (varDecl))
    : formula := Id.run do
      match f with
        | formula.string _ =>

          /-
          there can be only calls the preds here.
          These currently do not need replacers
          -/
          return f

        | formula.pred_with_args n pas =>
          formula.pred_with_args
            n
            (pas.map fun pa =>
              pa.replaceCalls callables)

        | formula.unaryRelBoolOperation op e =>
          formula.unaryRelBoolOperation
            op
            (e.replaceCalls callables)

        | formula.unaryLogicOperation op f =>
          formula.unaryLogicOperation
            op
            (f.replaceCalls callables)

        | formula.binaryLogicOperation op f1 f2 =>
          formula.binaryLogicOperation
            op
            (f1.replaceCalls callables)
            (f2.replaceCalls callables)

        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          formula.tertiaryLogicOperation
            op
            (f1.replaceCalls callables)
            (f2.replaceCalls callables)
            (f3.replaceCalls callables)

        | formula.algebraicComparisonOperation op ae1 ae2 =>
          formula.algebraicComparisonOperation op ae1 ae2

        | formula.relationComarisonOperation op e1 e2 =>
          formula.relationComarisonOperation
            op
            (e1.replaceCalls callables)
            (e2.replaceCalls callables)

        | formula.quantification q d n te forms =>
          formula.quantification
            q
            d
            n
            (te.replaceCalls callables)
            (forms.map fun f => f.replaceCalls callables)

  private def unhygienicUnfolder
    (input : Unhygienic (Term))
    : Term := Unhygienic.run do
    return ← input
  /--
  Generates a Lean term corosponding with the type
  -/
  private partial def toTerm'
    (f: formula)
    (blockName : Name)
    (variableNames : List (String)) -- to check if var or pred
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    -- names that have to be pure with no namespace (quantors and args)
    (pureNames : List (String) := [])
    : Except String (Unhygienic (Term)) := do

      match f with
      | formula.string s => do
        -- Quantors dont use namespaces
        if pureNames.contains s then
          return `($(mkIdent s.toName))

        else
          -- check if the ident is a variable or def
          if variableNames.contains s then
            return `((
                      ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
                    ))

          else
            return `((
                      ∻ $(mkIdent s!"{blockName}.preds.{s}".toName)
                    ))

      | formula.pred_with_args p pa => do
        let mut term :=
          `((
              ∻ $(mkIdent s!"{blockName}.preds.{p}".toName)
            ))

        let possibleCalledPredicates :=
          (callablePredicates.filter fun cp => cp.1.name == p)

        if possibleCalledPredicates.isEmpty || possibleCalledPredicates.length > 1 then
          panic!
            s!"Called Preds is Empty or more than one \
            in formulaService {possibleCalledPredicates}"

        let calledPredicate := possibleCalledPredicates.get! 0

        let calledArgsVarDecls :=
          (calledPredicate.1.predArgs.map fun cp =>
            cp.1.names.map fun _ =>
              cp.2).join

        for index in [0:pa.length] do

          --let definedArg := calledPredArgs.get! index

          let vd := calledArgsVarDecls.get! index

          let typeName :=
            (if vd.isRelation then
              vd.getFullRelationName
            else
              vd.getFullSignatureName)

          let typeReplacementName :=
            (if vd.isRelation then
              vd.getRelationReplacementName
            else
              vd.getSignatureReplacementName)

          let calledArg := pa.get! index
          let calledVarDecls_of_arg_to_cast ←
            calledArg.getCalledVariables callableVariables
          let calledVarDecls_of_arg_to_cast_joined :=
            (calledVarDecls_of_arg_to_cast.map fun a => a.2).join

          let cast_type_as_expr_string := expr.string typeName.toString
          let cast_type_as_expr_string_rb := cast_type_as_expr_string.toStringRb
          let cast_type_as_type_expr_relExpr := typeExpr.relExpr cast_type_as_expr_string_rb

          let cast_type_equals_called_var_type :=
            -- the type must be clear (only one called var)
            (calledVarDecls_of_arg_to_cast_joined.length == 1) &&
            /-
            get the type, stringify it and compare it to the
            replacerName of the type we try to cast to
            (the replacer is only needed because its "prettier"
            to use the alias for casting, otherwise you could use
            the replacer on both sides (its the actual name))
            -/
            (
              let cv := (calledVarDecls_of_arg_to_cast_joined.get! 0)
              cv.type.toString == typeReplacementName
            )

          if
            cast_type_as_expr_string == calledArg ||
            cast_type_as_expr_string_rb == calledArg ||
            cast_type_equals_called_var_type
          then
            term :=
              `(term |
                $(unhygienicUnfolder term)
                $(calledArg.toTermFromBlock blockName pureNames)
              )

          else

            let castCommand : Unhygienic Term :=
              `(term |
                cast
                ($(calledArg.toTermFromBlock blockName pureNames):term)
                ∷ $(cast_type_as_type_expr_relExpr.toSyntax blockName))

            term :=
              `(term |
                $(unhygienicUnfolder term)
                $(unhygienicUnfolder castCommand)
              )

        return term

      | formula.unaryRelBoolOperation op e =>
        return `(( $(op.toTerm)
            $(e.toTermFromBlock
              blockName pureNames)
          ))

      | formula.unaryLogicOperation op f =>
        let fTerm ← f.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        return `(term | ( $(op.toTerm) $(unhygienicUnfolder fTerm)))

      | formula.binaryLogicOperation op f1 f2 =>
        let f1Term ←
          f1.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        let f2Term ←
          f2.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        return `(( $(op.toTerm)
            $(unhygienicUnfolder f1Term)
            $(unhygienicUnfolder f2Term)
          ))

      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        let f1Term ←
          f1.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        let f2Term ←
          f2.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        let f3Term ←
          f3.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        return `(( $(op.toTerm)
            $(unhygienicUnfolder f1Term)
            $(unhygienicUnfolder f2Term)
            $(unhygienicUnfolder f3Term)
          ))

      | formula.algebraicComparisonOperation op ae1 ae2 =>
        return `(($(op.toTerm) $(ae1.toTerm blockName) $(ae2.toTerm blockName)))

      | formula.relationComarisonOperation op e1 e2 =>
        return `(( $(op.toTerm)
            $(e1.toTermFromBlock
              blockName pureNames)
            $(e2.toTermFromBlock
              blockName pureNames)
          ))

      | formula.quantification q disjunction n te f => do

        let names := (n.map fun (name) => mkIdent name.toName).reverse

        /-add quant vars here so you can get their type later-/
        let quantVarDecls :=
          n.map fun nam =>
            varDecl.mk
              (name := nam)
              (isQuantor := true)
              (isOpened := false)
              (openedFrom := "this")
              (isRelation := false)
              (relationOf := default)
              (type := te)
              (requiredDecls := [])

        -- one form ist present -> see syntax (+)
        let firstForm := f.get! 0
        let firstFTerm ←
          firstForm.toTerm'
            blockName variableNames (callableVariables ++ quantVarDecls) callablePredicates
            (pureNames.append n)

        let mut completefTerm : Unhygienic (Term) :=
          `(term | $(unhygienicUnfolder firstFTerm))

        for form in f.drop 1 do
          let fTerm ←
            form.toTerm'
              blockName variableNames (callableVariables ++ quantVarDecls) callablePredicates
              (pureNames.append n)

          completefTerm :=
            `(( $(unhygienicUnfolder completefTerm) ∧
                ($(unhygienicUnfolder fTerm))
              ))

        completefTerm :=
          `((
            $(mkIdent ``Formula.prop)
            ($(unhygienicUnfolder completefTerm))
            ))

        -- singular parameter is var constructor
        if names.length == 1 then
            return `(($(mkIdent ``Formula.var) $(q.toTerm)) (
              fun ( $(names.get! 0) : ∷ $((te.toStringRb).toSyntax blockName))
                => $(unhygienicUnfolder completefTerm)))

        -- multiple parameter is Group constructor
        else
          let mut formulaGroup :=
            `(($(mkIdent ``Group.var) (
              fun ( $(names.get! 0) : ∷ $((te.toStringRb).toSyntax blockName))
                => $(mkIdent ``Group.formula) $(unhygienicUnfolder completefTerm))))
          for n in (names.drop 1) do
            formulaGroup :=
              `(($(mkIdent ``Group.var) (
                fun ( $(n) : ∷ $((te.toStringRb).toSyntax blockName))
                  => $(unhygienicUnfolder formulaGroup))))
          if disjunction then
            formulaGroup :=
              `(( $(mkIdent ``Formula.disj)
                  $(mkIdent ``Shared.quant.all)
                  $(unhygienicUnfolder formulaGroup)
                ))
          else
            formulaGroup :=
              `(( $(mkIdent ``Formula.group)
                  $(mkIdent ``Shared.quant.all)
                  $(unhygienicUnfolder formulaGroup)
                ))

          return formulaGroup

  def toTerm
    (f: formula)
    (blockName : Name)
    (variableNames : List (String)) -- to check if var or pred
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    -- names that have to be pure with no namespace (quantors and args)
    (pureNames : List (String) := [])
    : Except String (Term) := do
    let x := toTerm' f blockName variableNames callableVariables callablePredicates pureNames
    match x with
      | Except.error msg => throw msg
      | Except.ok data => return unhygienicUnfolder data

  partial def toType_withoutIf
    (f : Formula_without_if)
    (signatureFactSigNames : List String := [])
    : formula :=
      match f with
        | `(formula| ( $fwi:formula_without_if )) =>
          toType_withoutIf fwi

        | `(formula| $name:ident) =>
          formula.string name.getId.toString

        | `(formula| $predName:ident [$predargs,*]) =>
          formula.pred_with_args predName.getId.toString
            (predargs.getElems.map fun (elem) =>
              expr.toType elem signatureFactSigNames).toList

        | `(formula| $op:unRelBoolOp $expression:expr ) =>
          formula.unaryRelBoolOperation
            (unRelBoolOp.toType op) (expr.toType expression signatureFactSigNames)

        | `(formula| $op:unLogOp $f:formula_without_if ) =>
          formula.unaryLogicOperation
            (unLogOp.toType op) (toType_withoutIf f)

        | `(formula| $form1:formula_without_if $op:binLogOp $form2:formula_without_if) =>
          formula.binaryLogicOperation
            (binLogOp.toType op) (toType_withoutIf form1) (toType_withoutIf form2)

        | `(formula|
            $algExpr1:algExpr
            $compOp:algCompareOp
            $algExpr2:algExpr) =>
          formula.algebraicComparisonOperation
            (algCompareOp.toType compOp)
            (algExpr.toType algExpr1)
            (algExpr.toType algExpr2)

        | `(formula|
            $expr1:expr
            $op:relCompareOp
            $expr2:expr) =>
          formula.relationComarisonOperation
            (relCompareOp.toType op)
            (expr.toType expr1 signatureFactSigNames)
            (expr.toType expr2 signatureFactSigNames)

        | `(formula|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula_without_if
            ) =>
          formula.quantification
          (quant.toType q)
          true
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          ([toType_withoutIf form])

        | `(formula|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            { $form:formula_without_if* }
            ) =>
          formula.quantification
          (quant.toType q)
          true
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          (form.map fun f => toType_withoutIf f).toList

        | `(formula|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula_without_if
            ) =>
          formula.quantification
          (quant.toType q)
          false
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          ([toType_withoutIf form])

        | `(formula|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            {$form:formula_without_if*}
            ) =>
          formula.quantification
          (quant.toType q)
          false
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          (form.map fun f => toType_withoutIf f).toList

        | _ => formula.unaryRelBoolOperation
                unRelBoolOp.no
                (expr.const constant.none) -- unreachable

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (f : Formula)
    (signatureFactSigNames : List String := [])
    : formula :=
      match f with
        | `(formula| $fwi:formula_without_if) =>
          toType_withoutIf fwi signatureFactSigNames
        | `(formula| $form1:formula => $form2:formula else $form3:formula) =>
            formula.tertiaryLogicOperation terLogOp.ifelse
              (toType form1) (toType form2) (toType form3)
        | _ => formula.unaryRelBoolOperation
                unRelBoolOp.no
                (expr.const constant.none) -- unreachable

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

  /--
  Returns the required variables for the formula to work in Lean
  -/
  partial def getReqVariables
    (f : formula)
    : List (String) := Id.run do
      match f with
        | formula.string _ => []
        | formula.pred_with_args _ pa =>
          (pa.map fun (e) => e.getReqVariables).join
        | formula.unaryRelBoolOperation _ e => e.getReqVariables
        | formula.unaryLogicOperation _ f => f.getReqVariables
        | formula.binaryLogicOperation _ f1 f2 =>
          f1.getReqVariables ++ f2.getReqVariables
        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          f1.getReqVariables ++ f2.getReqVariables ++ f3.getReqVariables
        | formula.algebraicComparisonOperation _ ae1 ae2 =>
          ae1.getReqVariables ++ ae2.getReqVariables
        | formula.relationComarisonOperation _ e1 e2 =>
          e1.getReqVariables ++ e2.getReqVariables
        | formula.quantification _ _ n e f =>
          (((f.map fun form =>
            form.getReqVariables).join)
            ++ e.getReqVariables).filter
            fun (elem) => !(n.contains elem) -- quantor vars are not required

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

        | _ => return []

  /--
  Gets all calls to the `callableVariables` which includes signatures and relations.

  The result is a list of the call (in string from) and a (possibly empty) list
  of the concrete possible called variables (in form of varDecls). If the inner
  list contains more than one varDecl, called variable is ambiguous and could
  be either.
  -/
  partial def getCalledVariables
    (f : formula)
    (callableVariables : List (varDecl))
    : Except String (List (String × List (varDecl))) := do

      match f with
        | formula.pred_with_args _ predicate_arguments =>
          let mut result : List (String × List varDecl) := []
          for pa in predicate_arguments do
            result := result ++ (← pa.getCalledVariables callableVariables)
          return result

        | formula.unaryRelBoolOperation _ e =>
          (e.getCalledVariables callableVariables)

        | formula.unaryLogicOperation _ f =>
          (f.getCalledVariables callableVariables)

        | formula.binaryLogicOperation _ f1 f2 =>
          let f1_calls ← (f1.getCalledVariables callableVariables)
          let f2_calls ← (f2.getCalledVariables callableVariables)
          return f1_calls ++ f2_calls

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          let f1_calls ← (f1.getCalledVariables callableVariables)
          let f2_calls ← (f2.getCalledVariables callableVariables)
          let f3_calls ← (f3.getCalledVariables callableVariables)
          return f1_calls ++ f2_calls ++ f3_calls

        | formula.relationComarisonOperation _ e1 e2 =>
          let e1_calls ← (e1.getCalledVariables callableVariables)
          let e2_calls ← (e2.getCalledVariables callableVariables)
          return e1_calls ++ e2_calls

        | formula.quantification _ _ names te f =>
          let typeExprRelCalls ← te.getCalledVariables callableVariables

          let quantVarDecls :=
            names.map fun n =>
              varDecl.mk
                (name := n)
                (isQuantor := true)
                (isOpened := false)
                (openedFrom := "this")
                (isRelation := false)
                (relationOf := default)
                (type := te)
                (requiredDecls := [])

          let mut result : List (String × List varDecl) := []
          for form in f do
            result := result ++ (← form.getCalledVariables (callableVariables ++ quantVarDecls))

          return typeExprRelCalls ++ result

        | _ => return []

  partial def simplifyDomainRestrictions
    (f : formula)
    (st : SymbolTable)
    : formula :=
    match f with
      | formula.pred_with_args p args =>
        pred_with_args p (args.map fun arg => arg.simplifyDomainRestrictions st)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation op (e.simplifyDomainRestrictions st)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation op (f.simplifyDomainRestrictions st)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.simplifyDomainRestrictions st)
          (f2.simplifyDomainRestrictions st)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
        op
        (f1.simplifyDomainRestrictions st)
        (f2.simplifyDomainRestrictions st)
        (f3.simplifyDomainRestrictions st)
      | formula.quantification q d n t f =>
        formula.quantification
        q
        d
        n
        (t.simplifyDomainRestrictions st)
        (f.map fun f => f.simplifyDomainRestrictions st)
      | _ => f

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
      | _ => f

  /--
  replaces calls to "this" (current module), with a call to the given module
  name.
  -/
  partial def replaceThisCalls
    (f : formula)
    (moduleName : String)
    : formula := Id.run do
    match f with
      | formula.pred_with_args p args =>
        pred_with_args
          p
          (args.map fun arg =>
            arg.replaceThisCalls moduleName)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation
          op
          (e.replaceThisCalls moduleName)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation
          op
          (f.replaceThisCalls moduleName)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.replaceThisCalls moduleName)
          (f2.replaceThisCalls moduleName)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
          op
          (f1.replaceThisCalls moduleName)
          (f2.replaceThisCalls moduleName)
          (f3.replaceThisCalls moduleName)
      | formula.quantification q d n t f =>
        formula.quantification
          q
          d
          n
          (t.replaceThisCalls moduleName)
          (f.map fun f =>
            f.replaceThisCalls moduleName)
      | _ => f

end Shared.formula
