/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Formula.formula
import ThoR.Shared.Syntax.Relation.Expr.expr_helper
import ThoR.Shared.Syntax.TypeExpr.typeExpr_helper

open Alloy

namespace Shared.formula

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given formula `f`
  -/
  partial def replaceCalls
    (f: formula)
    (callables : List (varDecl))
    : formula := Id.run do
      match f with
        | formula.string _ =>

          /-
          there can be only calls the preds here.
          These currently do not need replacers
          -/
          return f

        | formula.pred_with_args n pas =>
          formula.pred_with_args
            n
            (pas.map fun pa =>
              pa.replaceCalls callables)

        | formula.unaryRelBoolOperation op e =>
          formula.unaryRelBoolOperation
            op
            (e.replaceCalls callables)

        | formula.unaryLogicOperation op f =>
          formula.unaryLogicOperation
            op
            (f.replaceCalls callables)

        | formula.binaryLogicOperation op f1 f2 =>
          formula.binaryLogicOperation
            op
            (f1.replaceCalls callables)
            (f2.replaceCalls callables)

        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          formula.tertiaryLogicOperation
            op
            (f1.replaceCalls callables)
            (f2.replaceCalls callables)
            (f3.replaceCalls callables)

        | formula.algebraicComparisonOperation op ae1 ae2 =>
          formula.algebraicComparisonOperation op ae1 ae2

        | formula.relationComarisonOperation op e1 e2 =>
          formula.relationComarisonOperation
            op
            (e1.replaceCalls callables)
            (e2.replaceCalls callables)

        | formula.quantification q d n te forms =>
          formula.quantification
            q
            d
            n
            (te.replaceCalls callables)
            (forms.map fun f => f.replaceCalls callables)

end Shared.formula
