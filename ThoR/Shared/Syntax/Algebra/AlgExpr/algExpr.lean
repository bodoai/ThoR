/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Algebra.unAlgOp
import ThoR.Shared.Syntax.Algebra.binAlgOp
import ThoR.Shared.Syntax.Algebra.CardExpr.cardExpr

namespace Shared

  /--
  This inductive type represents an algebra expression
  -/
  inductive algExpr
    | number : (num : Int) → algExpr
    | cardExpr : (cardEx : cardExpr) → algExpr
    | unaryAlgebraOperation :
      (operator : unAlgOp) →
      (algExpr1 : algExpr) →
      algExpr
    | binaryAlgebraOperation :
      (operator : binAlgOp) →
      (algExpr1 : algExpr) →
      (algExpr2 : algExpr) →
      algExpr
  deriving Repr

  /--
  This syntax represents an algebra expression
  -/
  declare_syntax_cat algExpr
  syntax num : algExpr
  syntax cardExpr : algExpr
  syntax unAlgOp algExpr : algExpr
  syntax binAlgOp "[" algExpr "," algExpr "]" : algExpr

  namespace algExpr

    /--
    Generates a string representation of the type
    -/
    def toString (ae : algExpr) : String :=
      match ae with
        | algExpr.number n => ToString.toString n
        | algExpr.cardExpr ce => ce.toString
        | algExpr.unaryAlgebraOperation op ae => s!"{op} {toString ae}"
        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          s!"{op} [{toString ae1}, {toString ae2}]"

    instance : ToString algExpr where
      toString := toString

    instance : Inhabited algExpr where
      default := algExpr.number (1:Int)

  end algExpr

end Shared
