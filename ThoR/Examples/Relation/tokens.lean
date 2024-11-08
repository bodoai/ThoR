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
  class vars (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet] where
    Time    : ∷ set univ
    first   : ∷ one Time
    last    : ∷ one Time
    next    : ∷ Time lone → lone Time
    Node    : ∷ set univ
    Token   : ∷ set univ
    tokens  : ∷ (Node set → set Time) set → set Time
    succ    : ∷ Node set → one Node
end model1

#check model1.vars.Time

namespace model1.preds
  variable {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [model1.vars ThoR_TupleSet]

  def stutter (t t': ∷ one @model1.vars.Time)
    : Prop := ∻ model1.vars.tokens ⋈ t' ≡ ∻ model1.vars.tokens ⋈ t

  def send (t t' : ∷ one @model1.vars.Time)
           (n : ∷ one @model1.vars.Node)
   : Prop :=
    let n' := (n⋈ (∻ model1.vars.succ))
    let others := ∻ model1.vars.Node - n - n'
    ((n'⋈ ∻ model1.vars.tokens ⋈t') ≡ (n⋈(∻ model1.vars.tokens ⋈ t)) + (n'⋈(∻ model1.vars.tokens ⋈t )))
    ∧
    SetMultPredicates.no ((n⋈(∻ model1.vars.tokens ⋈ t')))
    ∧
    (others ⋈ (∻ model1.vars.tokens ⋈ t') ≡ others⋈(∻ model1.vars.tokens ⋈ t))
end model1.preds

namespace model1.facts
  variable {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [model1.vars ThoR_TupleSet]

    axiom ordering :
        (∻ model1.vars.Time ≡ ∻ model1.vars.first + ∻ model1.vars.first ⋈ ^∻ model1.vars.next)
        ∧
        (SetMultPredicates.no ((∻ model1.vars.last) ⋈ ∻ model1.vars.next))

    axiom ring : ∀ (n : ∷ one @model1.vars.Node),
      ∻ model1.vars.Node ⊂ (n⋈(^∻ model1.vars.succ))

    axiom init : SetMultPredicates.one (∻ model1.vars.tokens⋈∻ model1.vars.first)

    axiom traces :
        -- FIXME (t : Rel (RelType.mk.unary_rel Shared.mult.one
        --      (∻ model1.vars.Time-(@model1.vars.last R _ _))))
        -- FIXME let t' := t⋈∻ model1.vars.next
        -- in both FIXMEs: coercion from subtype to supertype
        ∀ (t : ∷ one @model1.vars.Time)
          (t': ∷ one @model1.vars.Time),
          (∻ model1.preds.stutter) t t'
          ∨
          (∃ (n : ∷ one @model1.vars.Node),
            (∻ model1.preds.send) t t' n
          )
end model1.facts

namespace model1.asserts
  variable {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [model1.vars ThoR_TupleSet]

  def tokenConservation : Prop :=
    ∀ (t : ∷ one @model1.vars.Time),
      SetMultPredicates.one (∻ model1.vars.tokens⋈t)
end model1.asserts

-- TODO Makro: "ThoR.TupleSet.init" erzeugt folgendes Kommando
variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]
-- TODO Makro: "ThoR.TupleSet.init model1.vars" erzeugt folgendes Kommando
variable [model1.vars ThoR_TupleSet]
-- TODO Makro: "ThoR.Alloy.init model1" erzeugt folgendes Kommando
-- variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet] [model1.vars ThoR_TupleSet]

theorem tokenConservation_correct :
  ∻ model1.asserts.tokenConservation := by
    unfold model1.asserts.tokenConservation
    intro t
    sorry

#print tokenConservation_correct
