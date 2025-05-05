/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.ArrowOp.arrowOp
import ThoR.Shared.Syntax.Mutuals.mutuals

open ThoR
open Lean

namespace Shared

  /--
  This syntax represents a typeExpression
  -/
  declare_syntax_cat typeExpr
  abbrev TypeExpr := TSyntax `typeExpr
  syntax arrowOp : typeExpr
  syntax expr : typeExpr
  syntax mult expr : typeExpr

end Shared
