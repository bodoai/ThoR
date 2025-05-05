/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Semantics.Semantics

import ThoR.Shared.Syntax.Mutuals.mutuals

open ThoR

namespace Shared
  mutual
    def expr.toSemantics
    -- TODO: move function attibutes??
      {R : Type} [TupleSet R]
      {n : ℕ}
      (e : expr)
      (RT : (RelType R n))
      (Relation : ThoR.Rel RT)
      : (Semantics.Expression RT) :=
      -- TODO: Correct return type so it accepts all exprs....
        match e with
          | expr.string s =>
            Semantics.Expression.rel Relation

          | expr.binaryRelOperation op e1 e2 =>
            match op with
              | _ => Semantics.Expression.rel Relation
              -- TODO: Correct return type so it accepts both
              /-
              | binRelOp.union =>
                Semantics.Expression.union Relation Relation
              | binRelOp.intersection =>
                Semantics.Expression.intersect Relation Relation
              | binRelOp.difference =>
                Semantics.Expression.diff Relation Relation
              | binRelOp.range_restriction =>
                Semantics.Expression.rangerestr Relation Relation
              | binRelOp.domain_restriction =>
                Semantics.Expression.domrestr Relation Relation
              | binRelOp.overwrite =>
                Semantics.Expression.append Relation Relation
              -/


          | _ => Semantics.Expression.rel Relation -- TODO: add missing cases
  end
end Shared
