/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOp
import ThoR.Shared.Syntax.Relation.Expr.exprService

open Alloy ThoR
open Lean

namespace Shared.arrowOp

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (op : ArrowOp)
    : Except String arrowOp := do
      match op with
        -- multArrowOpExpr
        | `(arrowOp| ($ae:arrowOp)) => return ← toType ae
        -- multArrowOpExpr
        | `(arrowOp|
            $subArrowExpr1:expr
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:expr) =>
          return arrowOp.multArrowOpExpr
            (← expr.toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← expr.toType subArrowExpr2)

        -- multArrowOpExprLeft
        | `(arrowOp|
            $subArrowExpr1:expr
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:arrowOp) =>
          return arrowOp.multArrowOpExprLeft
            (← expr.toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← toType subArrowExpr2)

        --multArrowOpExprRight
        | `(arrowOp|
            $subArrowExpr1:arrowOp
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:expr) =>
          return arrowOp.multArrowOpExprRight
            (← toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← expr.toType subArrowExpr2)

        --multArrowOp
        | `(arrowOp|
            $subArrowExpr1:arrowOp
            $[$mult1:mult]? $_:allowedArrows $[$mult2:mult]?
            $subArrowExpr2:arrowOp) =>
          return arrowOp.multArrowOp
            (← toType subArrowExpr1)
            (← mult.fromOption mult1)
            (← mult.fromOption mult2)
            (← toType subArrowExpr2)

        | syntx =>
            throw s!"No match implemented in \
            arrowOpService.toType \
            for '{syntx}'"

end Shared.arrowOp
