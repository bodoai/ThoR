/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

import Lean

open ThoR
open Lean PrettyPrinter Delaborator SubExpr

namespace model1
  structure vars (R : Type) [TupleSet R] where
    UNIV : Rel (RelType.mk.sig R Shared.mult.set)
    -- Time : set univ
    Time : Rel (RelType.mk.sig R Shared.mult.set)
    -- first : one Time
    first : Rel (RelType.mk.unary_rel Shared.mult.one Time)
    -- last : one Time
    last : Rel (RelType.mk.unary_rel Shared.mult.one Time)
    -- next : Time lone -> lone Time
    next : Rel (RelType.complex
      Time.getType Shared.mult.lone Shared.mult.lone Time.getType)
    -- Node : set univ
    Node : Rel (@RelType.sig R _ Shared.mult.set)
    -- Token : set univ
    Token : Rel (@RelType.sig R _ Shared.mult.set)
    -- tokens : Node set -> set Token set -> set Time
    tokens : Rel (RelType.complex
        (RelType.complex Node.getType Shared.mult.set Shared.mult.set Time.getType)
        Shared.mult.set
        Shared.mult.set
        Time.getType
      )
    -- succ : Node set -> one Node
    succ : Rel (
          RelType.complex
            (Node.getType) Shared.mult.set Shared.mult.one (Node.getType)
    )
end model1
namespace model1.facts
  variable (R : Type) [TupleSet R] (R' : model1.vars R)
    -- fact ordering {
    --    Time = first + first.^next
    --    no last.next
    -- }
    axiom ordering :
        ((model1.vars.Time R') ≡ (model1.vars.first R') + (model1.vars.first R') ⋈ ^(model1.vars.next R'))
        ∧
        (SetMultPredicates.no ((model1.vars.last R') ⋈ (model1.vars.next R')))
#check model1.facts.ordering
end model1.facts
#check model1.facts.ordering
