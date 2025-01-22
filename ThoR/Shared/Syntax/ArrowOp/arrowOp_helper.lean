/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOp
import ThoR.Shared.Syntax.Relation.Expr.expr_helper

open Alloy

namespace Shared.arrowOp

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given arrowOp `ao`
  -/
  def replaceCalls
    (ao: arrowOp)
    (callables :List (varDecl))
    : arrowOp :=
      match ao with
        | multArrowOpExpr e1 m1 m2 e2 =>
          multArrowOpExpr
            (e1.replaceCalls callables)
            m1
            m2
            (e2.replaceCalls callables)

        | multArrowOpExprLeft e m1 m2 ao1 =>
          multArrowOpExprLeft
            (e.replaceCalls callables)
            m1
            m2
            (ao1.replaceCalls callables)

        | multArrowOpExprRight ao1 m1 m2 e =>
          multArrowOpExprRight
            (ao1.replaceCalls callables)
            m1
            m2
            (e.replaceCalls callables)

        | multArrowOp ao1 m1 m2 ao2 =>
          multArrowOp
            (ao1.replaceCalls callables)
            m1
            m2
            (ao2.replaceCalls callables)

end Shared.arrowOp
