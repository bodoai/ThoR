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
  class vars (R : Type) [TupleSet R] where
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

#check model1.vars.UNIV

namespace model1.preds
  variable {R : Type} [TupleSet R] [model1.vars R]
  --  pred stutter [t, t': one Time] {
  --    tokens.t' = tokens·t
  --  }
  def stutter (t t': Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Time R _ _)))
    : Prop :=
    (@model1.vars.tokens R _ _) ⋈ t' ≡ (@model1.vars.tokens R _ _) ⋈ t
  -- @[app_unexpander stutter]
  -- def unexpStutter : Unexpander
  --   | `($pname $_) => `($pname)
  --   | _ => throw Unit.unit
  --  pred send [t, t': one Time, n: one Node] {
  --  let n' = n.succ |
  --  let others = Node - n - n' | {
  --    n'.(tokens.t') = n.(tokens.t) + n'.(tokens.t)
  --    n.(tokens.t') = none
  --    others.(tokens.t') = others.(tokens.t)
  --  }
  def send (t t' : Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Time R _ _)))
           (n : Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Node R _ _)))
   : Prop :=
    let n' := n⋈(@model1.vars.succ R _ _)
    let others := (@model1.vars.Node R _ _) - n - n'
    ((n'⋈((@model1.vars.tokens R _ _)⋈t')) ≡ (n⋈((@model1.vars.tokens R _ _)⋈t)) + (n'⋈((@model1.vars.tokens R _ _)⋈t)))
    ∧
    -- FIXME Vergleich r ≡ none führt auf Fehler
--    (n⋈((@model1.vars.tokens R _ _)⋈t') ≡ (Rel.constant.none R))
    SetMultPredicates.no (n⋈((@model1.vars.tokens R _ _)⋈t'))
    ∧
    (others⋈((@model1.vars.tokens R _ _)⋈t') ≡ others⋈((@model1.vars.tokens R _ _)⋈t))
  -- @[app_unexpander send]
  -- def unexpSend : Unexpander
  --   | `($pname $_) => `($pname)
  --   | _ => throw Unit.unit
end model1.preds

#check model1.preds.stutter
#print model1.preds.stutter

namespace model1.facts
  variable (R : Type) [TupleSet R] [model1.vars R]
    -- fact ordering {
    --    Time = first + first.^next
    --    no last.next
    -- }
    axiom ordering :
        ((@model1.vars.Time R _ _) ≡ (@model1.vars.first R _ _) + (@model1.vars.first R _ _) ⋈ ^(@model1.vars.next R _ _))
        ∧
        (SetMultPredicates.no ((@model1.vars.last R _ _) ⋈ (@model1.vars.next R _ _)))
    --   fact ring {all n:Node | Node ⊂ n.^succ}
    axiom ring : ∀ (n : Rel (
            RelType.mk.unary_rel Shared.mult.one (@model1.vars.Node R _ _)
          )
        ),
      (@model1.vars.Node R _ _) ⊂ (n⋈(^(@model1.vars.succ R _ _)))
    --  fact init {one tokens.first}
    axiom init : SetMultPredicates.one ((@model1.vars.tokens R _ _)⋈(@model1.vars.first R _ _))
  variable (R : Type) [TupleSet R] [model1.vars R]
    --  fact traces {
    --    all t : Time-last |
    --    let t' = t.next |
    --    stutter[t,t'] or (some n : Node | send[t,t',n])
    --  }
    axiom traces :
        ∀ -- FIXME (t : Rel (RelType.mk.unary_rel Shared.mult.one
          --      ((@model1.vars.Time R _ _)-(@model1.vars.last R _ _))))
          -- FIXME let t' := t⋈(@model1.vars.next R _ _)
          -- in both FIXMEs: coercion from subtype to supertype
          (t: Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Time R _ _)))
          (t': Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Time R _ _))),
          (@model1.preds.stutter R _ _) t t'
          ∨
          (∃ (n: Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Node R _ _))),
            (@model1.preds.send R _ _) t t' n
          )
  -- @[app_unexpander traces]
  -- def unexpTraces : Unexpander
  --   | `($aname $_) => `($aname)
  --   | _ => throw Unit.unit
end model1.facts

#check model1.facts.ordering
section xyz
  open model1
  open vars
  #check model1.facts.ordering
end xyz
#check model1.facts.ordering

namespace model1.facts
-- TODO eigener Print-Befehl für model1.facts etc.
#print model1.facts.traces

namespace model1.asserts
  variable {R : Type} [TupleSet R] [model1.vars R]
  --  assert tokenConservation {
  --    all t:Time | one (tokens.t)
  --  }
  def tokenConservation : Prop :=
    ∀ (t : Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Time R _ _))),
      SetMultPredicates.one ((@model1.vars.tokens R _ _)⋈t)
  -- @[app_unexpander tokenConservation]
  -- def unexpTokenConservation : Unexpander
  --   | `($fname $_) => `($fname)
  --   | _ => throw Unit.unit

  def stutterDoesNothing : Prop :=
    ∀ (t t': Rel (RelType.mk.unary_rel Shared.mult.one (@model1.vars.Time R _ _))),
      (@model1.preds.stutter R _ _) t t' → (@model1.preds.stutter R _ _) t t'
  -- @[app_unexpander stutterDoesNothing]
  -- def unexpStutterDoesNothing : Unexpander
  --   | `($fname $_) => `($fname)
  --   | _ => throw Unit.unit
end model1.asserts

#check model1.asserts.tokenConservation

theorem tokenConservation_correct (R : Type) [TupleSet R] [model1.vars R] :
  @model1.asserts.tokenConservation R _ _ := by
    unfold model1.asserts.tokenConservation
    intro t
    sorry

#print tokenConservation_correct

open model1
open vars
open preds
open asserts
theorem stutterDoesNothing_correct (R : Type) [TupleSet R] [model1.vars R] :
  @model1.asserts.stutterDoesNothing R _ _ := by
    unfold model1.asserts.stutterDoesNothing
--  ∀ (t t' : one Time), stutter t t' → stutter t t'
--  all t, t' : one Time | stutter[t, t'] → stutter[t, t']
    unfold stutter
    sorry
