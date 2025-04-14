/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.Mutuals.mutuals
import ThoR.Shared.Syntax.Relation.Expr.expr

open Lean

namespace Shared

  /--
  This syntax represents an algebra expression
  -/
  declare_syntax_cat algExpr
  abbrev AlgExpr := TSyntax `algExpr
  syntax num : algExpr
  syntax "# " expr : algExpr
  syntax unAlgOp algExpr : algExpr
  syntax binAlgOp "[" algExpr "," algExpr "]" : algExpr

  namespace algExpr

    /--
    Generates a string representation of the type
    -/
    def toString (ae : algExpr) : String :=
      match ae with
        | algExpr.number n => ToString.toString n
        | algExpr.cardExpression e => s!"# {e}"
        | algExpr.unaryAlgebraOperation op ae => s!"{op} {toString ae}"
        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          s!"{op} [{toString ae1}, {toString ae2}]"

    instance : ToString algExpr where
      toString := toString

    instance : Inhabited algExpr where
      default := algExpr.number (1:Int)

  end algExpr

end Shared
