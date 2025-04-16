/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import Lean

import ThoR.Basic

import ThoR.Shared.Syntax.constant
import ThoR.Alloy.Syntax.SeparatedNamespace
import ThoR.Shared.Syntax.Logic
import ThoR.Shared.Syntax.quant
import ThoR.Shared.Syntax.mult

import ThoR.Shared.Syntax.Relation.unRelOp
import ThoR.Shared.Syntax.Relation.binRelOp
import ThoR.Shared.Syntax.Relation.dotjoin
import ThoR.Shared.Syntax.Relation.relCompareOp
import ThoR.Shared.Syntax.Relation.unRelBoolOp

import ThoR.Shared.Syntax.Algebra.unAlgOp
import ThoR.Shared.Syntax.Algebra.binAlgOp
import ThoR.Shared.Syntax.Algebra.algCompareOp

open Alloy Lean

namespace Shared

  mutual
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
      | letDeclaration :
        (name : Name) →
        (value : formula) →
        (body : List (formula)) →
        formula
    deriving Repr, BEq

    /--
    This inductive type represents a relation
    -/
    inductive expr where
      | const : (const: constant) → expr
      | string : (string : String) → expr
      | function_call_with_args :
        (functionName : String) →
        (args : List (expr)) →
        expr
      | callFromOpen : (calledEntry : separatedNamespace) → expr
      | unaryRelOperation :
        (operator : unRelOp) →
        (expression : expr) →
        expr
      | binaryRelOperation :
        (operator : binRelOp) →
        (expression1 : expr) →
        (expression2 : expr) →
        expr
      | dotjoin :
        (dj : dotjoin) →
        (expression1 : expr) →
        (expression2 : expr) →
        expr
      | ifElse :
        (condition : formula) →
        (thenBody : expr) →
        (elseBody : expr) →
        expr
      | string_rb : (string : String) → expr
    deriving Repr, BEq

    /--
    This inductive type represents a typeExpression
    -/
    inductive typeExpr
      | arrowExpr : (arrowExpr : arrowOp) → typeExpr
      | multExpr :
          (m : mult) →
          (expr : expr) →
          typeExpr
      | relExpr :
          (expr : expr) →
          typeExpr
    deriving Repr, BEq

    /--
    This inductive type represents an algebra expression
    -/
    inductive algExpr
      | number : (num : Int) → algExpr
      | cardExpression : (expression : expr) → algExpr
      | unaryAlgebraOperation :
        (operator : unAlgOp) →
        (algExpr1 : algExpr) →
        algExpr
      | binaryAlgebraOperation :
        (operator : binAlgOp) →
        (algExpr1 : algExpr) →
        (algExpr2 : algExpr) →
        algExpr
    deriving Repr, BEq

    /--
    This inductive type represents an arrowOp
    -/
    inductive arrowOp
      | multArrowOpExpr :
          (e1 : expr) →
          (mult1 : mult) →
          (mult2 : mult) →
          (e2 : expr) →
          arrowOp
      | multArrowOpExprLeft :
          (e : expr) →
          (mult1 : mult) →
          (mult2 : mult) →
          (ao : arrowOp) →
          arrowOp
      | multArrowOpExprRight :
          (ao : arrowOp) →
          (mult1 : mult) →
          (mult2 : mult) →
          (e : expr) →
          arrowOp
      | multArrowOp :
          (ao1 : arrowOp) →
          (mult1 : mult) →
          (mult2 : mult) →
          (ao2 : arrowOp) →
          arrowOp
    deriving Repr, BEq

  end

  instance : Inhabited formula where
    default := formula.string "default formula"

  instance : Inhabited expr where
    default := expr.string "default expr"

  instance : Inhabited typeExpr where
    default := typeExpr.relExpr default

  instance : Inhabited algExpr where
    default := algExpr.number 0

  instance : Inhabited arrowOp where
    default := arrowOp.multArrowOpExpr default default default default

  /--
  This syntax represents an alloy formula
  -/
  declare_syntax_cat formula
  abbrev Formula := TSyntax `formula

  /--
  This syntax represents a relation
  -/
  declare_syntax_cat expr
  abbrev Expression := TSyntax `expr

  /--
  This syntax represents an  alloy expr (without if else)
  -/
  declare_syntax_cat expr_without_if
  abbrev Expr_without_if := TSyntax `expr_without_if

  mutual
    /--
    Generates a string representation of the type formula
    -/
    partial def formula.toString (f : formula) : String :=
      match f with
        | formula.string s => s
        | formula.pred_with_args p pa => Id.run do
          let mut pas := ""
          for a in pa do
            pas := pas.append s!"{a.toString} "
          s!"{p} ({pas})"
        | formula.unaryRelBoolOperation op e => s!"{op} {e.toString}"
        | formula.unaryLogicOperation op f => s!"{op} {f.toString}"
        | formula.binaryLogicOperation op f1 f2 =>
          s!"{f1.toString} {op} {f2.toString}"
        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          s!"{op} {f1.toString} {f2.toString} {f3.toString}"
        | formula.algebraicComparisonOperation op ae1 ae2 =>
          s!"{ae1.toString} {op} {ae2.toString}"
        | formula.relationComarisonOperation op e1 e2 =>
          s!"{e1.toString} {op} {e2.toString}"
        | formula.quantification q d n te f =>
          s!"{q} {if d then "disj" else ""} {n} : {te.toString} | {f.map fun e => e.toString}"
        | formula.letDeclaration name value body =>
          let bodyString := body.map fun e => e.toString
          s!"let {name} := {value.toString} | ⦃{bodyString}⦄"

    /--
    Generates a string representation of the type expr
    -/
    partial def expr.toString (e : expr) : String :=
      match e with
        | expr.const c => c.toString
        | expr.string s => s
        | expr.function_call_with_args function_name args =>
          s!"{function_name} {args.map fun arg => arg.toString}"
        | expr.callFromOpen sn => sn.toString
        | expr.unaryRelOperation op e => (op.toString) ++ (e.toString)
        | expr.binaryRelOperation op e1 e2 =>
          (e1.toString) ++ (op.toString) ++ (e2.toString)
        | expr.dotjoin dj e1 e2 =>
          s!"{e1.toString}{dj}{e2.toString}"
        | expr.ifElse condition thenBody elseBody =>
          s!"{condition.toString} => {thenBody.toString} else {elseBody.toString}"
        | expr.string_rb s => s

    /--
    Generates a string representation of the type algExpr
    -/
    partial def algExpr.toString (ae : algExpr) : String :=
      match ae with
        | algExpr.number n => ToString.toString n
        | algExpr.cardExpression e => s!"# {e.toString}"
        | algExpr.unaryAlgebraOperation op ae => s!"{op} {ae.toString}"
        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          s!"{op} [{ae1.toString}, {ae2.toString}]"

    /--
    Generates a string representation of the type
    -/
    partial def typeExpr.toString (te : typeExpr) : String :=
      match te with
        | typeExpr.arrowExpr ae => ae.toString
        | typeExpr.multExpr m e => (m.toString) ++ " " ++ (e.toString)
        | typeExpr.relExpr e => e.toString

    /--
    Generates a string representation of the type
    -/
    partial def arrowOp.toString (ae : arrowOp) : String :=
      match ae with
        | arrowOp.multArrowOpExpr ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

        | arrowOp.multArrowOpExprLeft ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

        | arrowOp.multArrowOpExprRight ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

        | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
          (ae1.toString) ++ " " ++ (m1.toString)
          ++ " → " ++
          (m2.toString) ++ " " ++ (ae2.toString)

  end

  instance : ToString arrowOp where
    toString := arrowOp.toString

  instance : ToString typeExpr where
    toString := typeExpr.toString

  instance : ToString algExpr where
    toString := algExpr.toString

  instance : ToString expr where
    toString := expr.toString

  instance : ToString formula where
    toString := formula.toString

end Shared
