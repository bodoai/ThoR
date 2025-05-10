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

end Shared
