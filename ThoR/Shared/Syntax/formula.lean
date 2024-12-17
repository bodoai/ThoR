/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
an alloy formula is used as the body of predicates, facts and asserts
-/
import ThoR.Relation
import ThoR.Shared.Syntax.Algebra
import ThoR.Shared.Syntax.Logic
import ThoR.Shared.Syntax.quant
import ThoR.Shared.Syntax.baseType
import ThoR.Shared.Syntax.Relation

open Lean
open ThoR.Quantification

namespace Shared

  /--
  This inductive type represents an alloy formula
  -/
  inductive formula
    | string : (string : String) → formula
    | pred_with_args :
      (ident : String) →
      (args : List (expr))
      →  formula
    | unaryRelBoolOperation :
      (operator : unRelBoolOp) →
      (expr : expr) →
      formula
    | unaryLogicOperation :
      (operator : unLogOp) →
      (form : formula) →
      formula
    | binaryLogicOperation :
      (operator : binLogOp) →
      (form1 : formula) →
      (form2 : formula) →
      formula
    | tertiaryLogicOperation :
      (operator : terLogOp) →
      (form1 : formula) →
      (form2 : formula) →
      (form3 : formula) →
      formula
    | algebraicComparisonOperation :
      (operator : algCompareOp) →
      (algExpr1 : algExpr) →
      (algExpr2 : algExpr) →
      formula
    | relationComarisonOperation :
      (operator : relCompareOp) →
      (expression1 : expr) →
      (expression2 : expr) →
      formula
    | quantification :
      (quantifier : quant) →
      (disjunction : Bool) →
      (names : List (String)) →
      (typeExpression : typeExpr) →
      (formulas : List formula) →
      formula
  deriving Repr

  /--
  This syntax represents an alloy formula
  -/
  declare_syntax_cat formula
  syntax ident : formula

  syntax ident ( "[" expr,+ "]") : formula  -- predcall

  syntax "("formula")" : formula

  syntax unRelBoolOp expr : formula

  syntax unLogOp formula: formula

  syntax formula binLogOp formula : formula
  syntax expr relCompareOp expr : formula

  syntax algExpr algCompareOp algExpr : formula
  syntax quant ("disj")? ident,+ ":" typeExpr "|" "{" (formula)+ "}" : formula
  syntax quant ("disj")? ident,+ ":" typeExpr "|" formula : formula

  --Special tertiariy Syntax
  syntax "if " formula " then " formula " else " formula : formula

  instance : Inhabited formula where
    default := formula.string ""

  namespace formula

    /--
    Generates a string representation of the type
    -/
    partial def toString (f : formula) : String :=
      match f with
        | formula.string s => s
        | formula.pred_with_args p pa => Id.run do
          let mut pas := ""
          for a in pa do
            pas := pas.append s!"{a} "
          s!"{p} ({pas})"
        | formula.unaryRelBoolOperation op e => s!"{op} {e}"
        | formula.unaryLogicOperation op f => s!"{op} {toString f}"
        | formula.binaryLogicOperation op f1 f2 =>
          s!"{toString f1} {op} {toString f2}"
        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          s!"{op} {toString f1} {toString f2} {toString f3}"
        | formula.algebraicComparisonOperation op ae1 ae2 =>
          s!"{ae1} {op} {ae2}"
        | formula.relationComarisonOperation op e1 e2 =>
          s!"{e1} {op} {e2}"
        | formula.quantification q d n te f =>
          s!"{q} {if d then "disj" else ""} {n} : {te} | {f.map fun e => e.toString}"

    instance : ToString formula where
      toString := toString

    /--
    Generates a Lean term corosponding with the type
    -/
    partial def toTerm
      (f: formula)
      (blockName : Name)
      (variableNames : List (String)) -- to check if var or pred
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
                blockName variableNames pureNames
                )
            ))

        | formula.binaryLogicOperation op f1 f2 =>
          `(( $(op.toTerm)
              $(f1.toTerm
                blockName variableNames pureNames
                )
              $(f2.toTerm
                blockName variableNames pureNames
                )
            ))

        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          `(( $(op.toTerm)
              $(f1.toTerm
                blockName variableNames pureNames
                )
              $(f2.toTerm
                blockName variableNames pureNames
                )
              $(f3.toTerm
                blockName variableNames pureNames
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
                blockName variableNames
                (pureNames.append n)
              ))

          for form in f.drop 1 do
            fTerm ←
              `(( $fTerm ∧
                  ($(form.toTerm
                    blockName variableNames
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
    Returns all calls of predicats in the given formula.

    These are returned as a List of Lists. The inner lists contain the
    name of the pred followed by the arguments.
    -/
    partial def getPredCalls (f : formula) : Option (List (String)) :=
      match f with
        | formula.string s => (Option.some [s])
        | formula.pred_with_args p pa =>
          (Option.some ([p].append (pa.map fun (e) => e.toString)))
        | formula.unaryLogicOperation _ f => f.getPredCalls
        | formula.binaryLogicOperation _ f1 f2 => do
          let f1pc := f1.getPredCalls
          let f2pc := f2.getPredCalls

          match f1pc, f2pc with
            | Option.some f1pcs, Option.some f2pcs =>
              return (f1pcs ++ f2pcs)
            | Option.some f1pcs, Option.none =>
              return f1pcs
            | Option.none , Option.some f2pcs =>
              return f2pcs
            | _, _ => Option.none

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          let f1pc := f1.getPredCalls
          let f2pc := f2.getPredCalls
          let f3pc := f3.getPredCalls

          match f1pc, f2pc, f3pc with
            | Option.some f1pcs, Option.some f2pcs, Option.some f3pcs =>
              return (f1pcs ++ f2pcs ++ f3pcs)
            | Option.some f1pcs, Option.some f2pcs, Option.none =>
              return (f1pcs ++ f2pcs)
            | Option.some f1pcs, Option.none , Option.none =>
              return f1pcs
            | Option.some f1pcs, Option.none , Option.some f3pcs =>
              return (f1pcs ++ f3pcs)
            | Option.none, Option.some f2pcs, Option.some f3pcs =>
              return (f2pcs ++ f3pcs)
            | _, _, _ => Option.none

        | formula.quantification _ _ _ _ f => do
          let mut result : List String := []
          for form in f do
            let opc := form.getPredCalls
            if opc.isSome then
              result := result.append opc.get!
          if result.isEmpty then
            Option.none
          else
            return result

        | _ => Option.none

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
            formula.string name.getId.lastComponentAsString

          | `(formula| $predName:ident [$predargs,*]) =>
            formula.pred_with_args predName.getId.lastComponentAsString
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
            (names.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList
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
            (names.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList
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
            (names.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList
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
            (names.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList
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

    partial def replaceRelationCalls
      (f: formula)
      (relationNames :List (String))
      (replacementNames :List (String))
      : formula := Id.run do
        match f with
          | formula.string s =>
            let index := relationNames.indexOf s
            if index == relationNames.length then
              f
            else
              formula.string (replacementNames.get! index)

          | formula.pred_with_args n pas =>
            formula.pred_with_args
              n
              (pas.map fun pa =>
                pa.replaceRelationCalls relationNames replacementNames)

          | formula.unaryRelBoolOperation op e =>
            formula.unaryRelBoolOperation
              op
              (e.replaceRelationCalls relationNames replacementNames)

          | formula.unaryLogicOperation op f =>
            formula.unaryLogicOperation
              op
              (f.replaceRelationCalls relationNames replacementNames)

          | formula.binaryLogicOperation op f1 f2 =>
            formula.binaryLogicOperation
              op
              (f1.replaceRelationCalls relationNames replacementNames)
              (f2.replaceRelationCalls relationNames replacementNames)

          | formula.tertiaryLogicOperation op f1 f2 f3 =>
            formula.tertiaryLogicOperation
              op
              (f1.replaceRelationCalls relationNames replacementNames)
              (f2.replaceRelationCalls relationNames replacementNames)
              (f3.replaceRelationCalls relationNames replacementNames)

          | formula.algebraicComparisonOperation op ae1 ae2 =>
            formula.algebraicComparisonOperation op ae1 ae2

          | formula.relationComarisonOperation op e1 e2 =>
            formula.relationComarisonOperation
              op
              (e1.replaceRelationCalls relationNames replacementNames)
              (e2.replaceRelationCalls relationNames replacementNames)

          | formula.quantification q d n te forms =>
            formula.quantification
              q
              d
              n
              (te.replaceRelationCalls relationNames replacementNames)
              (forms.map fun f => f.replaceRelationCalls relationNames replacementNames)

  end formula

end Shared
