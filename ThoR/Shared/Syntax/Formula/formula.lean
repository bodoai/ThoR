/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
an alloy formula is used as the body of predicates, facts and asserts
-/

import ThoR.Shared.Syntax.Algebra
import ThoR.Shared.Syntax.Logic
import ThoR.Shared.Syntax.quant
import ThoR.Shared.Syntax.Relation
import ThoR.Shared.Syntax.TypeExpr.typeExpr

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

  end formula

end Shared
