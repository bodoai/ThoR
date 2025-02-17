/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Formula.formula
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl

import ThoR.Shared.Syntax.Relation.Expr.exprService
import ThoR.Shared.Syntax.TypeExpr.typeExprService
import ThoR.Shared.Syntax.Algebra.AlgExpr.algExprService

import ThoR.Relation.Elab
import ThoR.Relation.Quantification

open Alloy ThoR ThoR.Quantification
open Lean

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

  /--
  Generates a Lean term corosponding with the type
  -/
  partial def toTerm
    (f: formula)
    (blockName : Name)
    (variableNames : List (String)) -- to check if var or pred
    (callablePreds : List (predDecl))
    -- names that have to be pure with no namespace (quantors and args)
    (pureNames : List (String) := [])
    : TSyntax `term := Unhygienic.run do

      match f with
      | formula.string s => do
        -- Quantors dont use namespaces
        if pureNames.contains s then
          `($(mkIdent s.toName))

        else
          -- check if the ident is a variable or def
          if variableNames.contains s then
            `((
              ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
            ))

          else
            `((
              ∻ $(mkIdent s!"{blockName}.preds.{s}".toName)
            ))

      | formula.pred_with_args p pa => do
        let mut term ←
          `((
              ∻ $(mkIdent s!"{blockName}.preds.{p}".toName)
            ))

        for arg in pa do
          term ← `($term $(arg.toTermFromBlock blockName pureNames))

        return term

      | formula.unaryRelBoolOperation op e =>
        `(( $(op.toTerm)
            $(e.toTermFromBlock
              blockName pureNames)
          ))

      | formula.unaryLogicOperation op f =>
        `(( $(op.toTerm)
            $(f.toTerm
              blockName variableNames callablePreds pureNames
              )
          ))

      | formula.binaryLogicOperation op f1 f2 =>
        `(( $(op.toTerm)
            $(f1.toTerm
              blockName variableNames callablePreds pureNames
              )
            $(f2.toTerm
              blockName variableNames callablePreds pureNames
              )
          ))

      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        `(( $(op.toTerm)
            $(f1.toTerm
              blockName variableNames callablePreds pureNames
              )
            $(f2.toTerm
              blockName variableNames callablePreds pureNames
              )
            $(f3.toTerm
              blockName variableNames callablePreds pureNames
              )
          ))
      | formula.algebraicComparisonOperation op ae1 ae2 =>
        `(($(op.toTerm) $(ae1.toTerm) $(ae2.toTerm)))

      | formula.relationComarisonOperation op e1 e2 =>
        `(( $(op.toTerm)
            $(e1.toTermFromBlock
              blockName pureNames)
            $(e2.toTermFromBlock
              blockName pureNames)
          ))

      | formula.quantification q disjunction n te f => do

        let names := (n.map fun (name) => mkIdent name.toName).reverse

        -- one form ist present -> see syntax (+)
        let firstForm := f.get! 0
        let mut fTerm ←
          `($(firstForm.toTerm
              blockName variableNames callablePreds
              (pureNames.append n)
            ))

        for form in f.drop 1 do
          fTerm ←
            `(( $fTerm ∧
                ($(form.toTerm
                  blockName variableNames callablePreds
                  (pureNames.append n)
                ))
              ))

        fTerm ←
          `((
            $(mkIdent ``Formula.prop)
            ($fTerm)
            ))

        -- singular parameter is var constructor
        if names.length == 1 then
            `(($(mkIdent ``Formula.var) $(q.toTerm)) (
              fun ( $(names.get! 0) : ∷ $((te.toStringRb).toSyntax blockName))
                => $fTerm))

        -- multiple parameter is Group constructor
        else
          let mut formulaGroup ←
            `(($(mkIdent ``Group.var) (
              fun ( $(names.get! 0) : ∷ $((te.toStringRb).toSyntax blockName))
                => $(mkIdent ``Group.formula) $fTerm)))
          for n in names.drop 1 do
            formulaGroup ←
              `(($(mkIdent ``Group.var) (
                fun ( $(n) : ∷ $((te.toStringRb).toSyntax blockName))
                  => $formulaGroup)))
          if disjunction then
            formulaGroup ← `(($(mkIdent ``Formula.disj) $(mkIdent ``Shared.quant.all) $formulaGroup))
          else
            formulaGroup ← `(($(mkIdent ``Formula.group) $(mkIdent ``Shared.quant.all) $formulaGroup))
          return formulaGroup

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (f : TSyntax `formula)
    (signatureFactSigNames : List String := [])
    : formula :=
      match f with
        | `(formula| ( $f:formula )) => toType f

        | `(formula| $name:ident) =>
          formula.string name.getId.toString

        | `(formula| $predName:ident [$predargs,*]) =>
          formula.pred_with_args predName.getId.toString
            (predargs.getElems.map fun (elem) =>
              expr.toType elem signatureFactSigNames).toList

        | `(formula| $op:unRelBoolOp $expression:expr ) =>
          formula.unaryRelBoolOperation
            (unRelBoolOp.toType op) (expr.toType expression signatureFactSigNames)

        | `(formula| $op:unLogOp $f:formula ) =>
          formula.unaryLogicOperation
            (unLogOp.toType op) (toType f)

        | `(formula| $form1:formula $op:binLogOp $form2:formula) =>
          formula.binaryLogicOperation
            (binLogOp.toType op) (toType form1) (toType form2)

        | `(formula| if $form1 then $form2 else $form3) =>
          formula.tertiaryLogicOperation terLogOp.ifelse
            (toType form1) (toType form2) (toType form3)

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
            $form:formula
            ) =>
          formula.quantification
          (quant.toType q)
          true
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          ([toType form])

        | `(formula|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            { $form:formula* }
            ) =>
          formula.quantification
          (quant.toType q)
          true
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          (form.map fun f => toType f).toList

        | `(formula|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula
            ) =>
          formula.quantification
          (quant.toType q)
          false
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          ([toType form])

        | `(formula|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            {$form:formula*}
            ) =>
          formula.quantification
          (quant.toType q)
          false
          (names.getElems.map fun (elem) => elem.getId.toString).toList
          (typeExpr.toType typeExpression)
          (form.map fun f => toType f).toList

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
    : (List (commandDecl × List (expr × List (List (varDecl))))) := Id.run do
      let callablePredicateNames := callablePredicates.map fun cp => cp.name

      match f with
        | formula.string s =>
          if callablePredicateNames.contains s then
            let index := callablePredicateNames.indexOf s
            let calledPredicate := callablePredicates.get! index
            [(calledPredicate, [])]
          else
            []

        | formula.pred_with_args predicate_name predicate_arguments =>
          if callablePredicateNames.contains predicate_name then
            let index := callablePredicateNames.indexOf predicate_name
            let calledPredicate := callablePredicates.get! index
            let calledArgumentVariables :=
              (predicate_arguments.map
                fun argument => (argument ,(argument.getCalledVariables callableVariables))
              )

            [(calledPredicate, calledArgumentVariables)]
          else
            []

        | formula.unaryLogicOperation _ f =>
          f.getCalledPredicates callablePredicates callableVariables

        | formula.binaryLogicOperation _ f1 f2 =>
          (f1.getCalledPredicates callablePredicates callableVariables) ++
          (f2.getCalledPredicates callablePredicates callableVariables)

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          (f1.getCalledPredicates callablePredicates callableVariables) ++
          (f2.getCalledPredicates callablePredicates callableVariables) ++
          (f3.getCalledPredicates callablePredicates callableVariables)

        | formula.quantification _ _ _ _ f =>
           (f.map fun form =>
              form.getCalledPredicates callablePredicates callableVariables).join

        | _ => []

  /--
  Gets all calls to the `callableVariables` which includes signatures and relations.

  Returns a list of the called Variables
  -/
  partial def getCalledVariables
    (f : formula)
    (callableVariables : List (varDecl))
    : List (List (varDecl)) := Id.run do

      match f with
        | formula.pred_with_args _ predicate_arguments =>
          (predicate_arguments.map
            fun pa => pa.getCalledVariables callableVariables).join

        | formula.unaryRelBoolOperation _ e =>
          (e.getCalledVariables callableVariables)

        | formula.unaryLogicOperation _ f =>
          (f.getCalledVariables callableVariables)

        | formula.binaryLogicOperation _ f1 f2 =>
          (f1.getCalledVariables callableVariables) ++
          (f2.getCalledVariables callableVariables)

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          (f1.getCalledVariables callableVariables) ++
          (f2.getCalledVariables callableVariables) ++
          (f3.getCalledVariables callableVariables)

        | formula.relationComarisonOperation _ e1 e2 =>
          (e1.getCalledVariables callableVariables) ++
          (e2.getCalledVariables callableVariables)

        | formula.quantification _ _ names te f =>
          let typeExprRelCalls := te.getCalledVariables callableVariables

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

          typeExprRelCalls ++
          (f.map fun form =>
              form.getCalledVariables (callableVariables ++ quantVarDecls)).join

        | _ => []

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

end Shared.formula
