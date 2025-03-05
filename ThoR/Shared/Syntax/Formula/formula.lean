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

  -- introduce let syntax
  syntax letDecl : formula

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

    partial def compare (formula1 formula2 : formula) : Bool :=
      match formula1, formula2 with
        | formula.string s1, formula.string s2 =>
          s1 == s2

        | formula.pred_with_args p1 pa1,
          formula.pred_with_args p2 pa2 =>
          p1 == p2 && pa1 == pa2

        | formula.unaryRelBoolOperation op1 e1,
          formula.unaryRelBoolOperation op2 e2 =>
          op1 == op2 && e1 == e2

        | formula.unaryLogicOperation op1 f1,
          formula.unaryLogicOperation op2 f2 =>
          op1 == op2 &&
          compare f1 f2

        | formula.binaryLogicOperation op1 fa1 fa2,
          formula.binaryLogicOperation op2 fb1 fb2 =>
          op1 == op2 &&
          compare fa1 fb1 &&
          compare fa2 fb2

        | formula.tertiaryLogicOperation op1 fa1 fa2 fa3,
          formula.tertiaryLogicOperation op2 fb1 fb2 fb3 =>
          op1 == op2 &&
          compare fa1 fb1 &&
          compare fa2 fb2 &&
          compare fa3 fb3

        | formula.algebraicComparisonOperation op1 algExprA1 algExprA2,
          formula.algebraicComparisonOperation op2 algExprB1 algExprB2 =>
          op1 == op2 &&
          algExprA1 == algExprA2 &&
          algExprB1 == algExprB2

        | formula.relationComarisonOperation op1 ea1 ea2,
          formula.relationComarisonOperation op2 eb1 eb2 =>
          op1 == op2 &&
          ea1 == eb1 &&
          ea2 == eb2

        | formula.quantification q1 d1 n1 te1 f1,
          formula.quantification q2 d2 n2 te2 f2 =>
          let fx := f1.zip f2
          q1 == q2 &&
          d1 == d2 &&
          n1 == n2 &&
          te1 == te2 &&
          fx.all fun f => compare f.1 f.2

        | _ , _ => false

    instance : BEq formula where
      beq := compare

  end formula

end Shared
