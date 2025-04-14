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
    deriving Repr, Inhabited, BEq

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
    deriving Repr

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

end Shared
