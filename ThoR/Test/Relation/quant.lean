/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Quantification
import ThoR.Relation.Rel
import ThoR.Alloy.Delab

open ThoR
open ThoR.Quantification
open ThoR.Quantification.Formula

variable {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet]
variable (Time : ∷ set univ)
variable (Node : ∷ set univ)

#check Time.getType

#check Formula.prop
def F0 := Formula.prop True

-- all t : Time | t ≡ t
def F1 :=
  Formula.var Shared.quant.all (
      fun (t : ∷ Time) => (
                    Formula.prop ((t ≡ t))
                  )
                )

#print F1
#check (F1 Time).eval

theorem ex1: (F1 Time) := by
  unfold F1
  unfold Formula.eval
  dsimp
  unfold Formula.evalAll Formula.eval
  unfold HEqual.hEqual
  unfold Rel.instHEqual
  dsimp
  simp


-- all t : Time | all n : Node | t ≡ n
def F2 := Formula.var Shared.quant.all (
  fun (t : ∷ Time) => (
    Formula.var Shared.quant.all (
      fun (n : ∷ Node) => (
                    Formula.prop ((t ≡ n))
      )
    )
  )
)
#print F2
#check F2
theorem ex2: ¬ (F2 Time Node) := by
  unfold Formula.eval F2
  dsimp
  unfold Formula.evalAll
  dsimp
  unfold Formula.eval
  dsimp
  unfold Formula.evalAll
  dsimp
  unfold Formula.eval
  intro contra
  sorry

-- all t : Time  | all n, n' : Node | t ≡ n ∧ t ≡ n'
def F3 := Formula.var Shared.quant.all (
  fun (t : ∷ Time) => (
    Formula.group Shared.quant.all (
      Group.var
        fun (n : ∷ Node) => (
          Group.var
            fun (n' : ∷ Node) => (
              Group.formula (
                        Formula.prop ((t ≡ n) ∧ (t ≡ n'))
              )
            )
        )
    )
    )
  )
#print F3

-- all n, n', n'' : Node | True
def F4 := Formula.disj Shared.quant.all (
      Group.var
        fun (n : ∷ Node) => (
          Group.var
            fun (n' : ∷ Node) => (
              Group.var
                fun (n'' : ∷ Node) => (
                  Group.formula (
                            Formula.prop (True)
                  )
                )
            )
        )
    )
#print F4
#check F4
theorem ex4: (F4 Node) := by
  unfold F4
  unfold Formula.eval; dsimp
  repeat unfold Formula.evalDisjAll
  sorry

-- some disj n, n',n'' : Node | True
def F5 := Formula.disj Shared.quant.some (
      Group.var
        fun (n : ∷ Node) => (
          Group.var
            fun (n' : ∷ Node) => (
              Group.var
                fun (n'' : ∷ Node) => (
                  Group.formula (
                            Formula.prop (True)
                  )
                )
            )
        )
    )
#print F5
#check F5
theorem ex5: (F5 Node) := by
  unfold F5
  unfold Formula.eval; dsimp
  repeat unfold Formula.evalDisjSome
  sorry

-- some disj n, n', n'' : Node | all disj n, n', n'' : Node | True
def F6 := Formula.disj Shared.quant.some (
      Group.var
        fun (n : ∷ Node) => (
          Group.var
            fun (n' : ∷ Node) => (
              Group.var
                fun (n'' : ∷ Node) => (
                  Group.formula (
                    Formula.disj Shared.quant.all (
                          Group.var
                            fun (n : ∷ Node) => (
                              Group.var
                                fun (n' : ∷ Node) => (
                                  Group.var
                                    fun (n'' : ∷ Node) => (
                                      Group.formula (
                                                Formula.prop (True)
                                      )
                                    )
                                )
                            )
                    )
                    )
                )
            )
        )
    )
#print F6
#check F6
theorem ex6: (F6 Node) := by
  unfold F6
  unfold Formula.eval; dsimp
  repeat unfold Formula.evalDisjSome
  unfold Formula.eval; dsimp
  repeat unfold Formula.evalDisjAll
  sorry

def F7 := Formula.disj Shared.quant.all (
      Group.var
        fun (n : ∷ Node) => (
          Group.var
            fun (n' : ∷ Node) => (
              Group.var
                fun (n'' : ∷ Node) => (
                  Group.formula (
                    Formula.disj Shared.quant.some (
                          Group.var
                            fun (t : ∷ Time) => (
                              Group.var
                                fun (t' : ∷ Time) => (
                                  Group.var
                                    fun (t'' : ∷ Time) => (
                                      Group.formula (
                                                Formula.prop (n+n'+n'' ≡ t+t'+t'')
                                      )
                                    )
                                )
                            )
                    )
                    )
                )
            )
        )
    )
#print F7
theorem ex7: (F7 Node Time) := by
  unfold F7
  unfold Formula.eval; dsimp
  repeat unfold Formula.evalDisjAll
  unfold Formula.eval; dsimp
  repeat unfold Formula.evalDisjSome
  sorry

def F8 := Formula.disj Shared.quant.lone (
          Group.var
            fun (n' : ∷ Node) => (
              Group.var
                fun (n'' : ∷ Node) => (
                  Group.formula (
                            Formula.prop (True)
                  )
                )
            )
        )
#print F8
#check F8
theorem ex8: (F8 Node) := by
  unfold F8
  unfold Formula.eval
  repeat unfold Formula.evalDisjLone
  unfold Formula.eval
  sorry

namespace All
  theorem intro {T T': Type} (f : T → Formula T'):
    (∀ x, f x) →
    Formula.var Shared.quant.all (f) := by
  intro h
  unfold Formula.eval
  dsimp
  unfold Formula.evalAll
  apply h

  theorem elim {T T' : Type} {f : T → Formula T'}:
    Formula.var Shared.quant.all (f) → ∀ x, f x := by
  intro h
  unfold Formula.eval at h; dsimp at h
  unfold Formula.evalAll at h
  apply h
end All

lemma l2 : (F2 Time Node) := by
  unfold F2
  apply All.intro; intro x
  apply All.intro; intro x'
  unfold Formula.eval
  sorry

-- Reihenfolge n<->t absichtlich vertauscht
def pred2 (n : ∷ Node) (t : ∷ Time) := t ≡ n
#check pred2 Time Node
def F2' := Formula.var Shared.quant.all (
  fun (t : ∷ Time) => (
    Formula.var Shared.quant.all (
      fun (n : ∷ Node) => (
                    Formula.prop (pred2 Time Node n t)
      )
    )
  )
)
#print F2
lemma l2' : (F2' Time Node) := by
  unfold F2'
  apply All.intro; intro t -- -> 1 Beweistaktik
  apply All.intro; intro n
  unfold Formula.eval
  sorry

namespace Some
  theorem elim {T T' : Type} (f : T → Formula T'):
    (∃ x, f x) →
    Formula.var Shared.quant.some (f) := by
  intro h
  unfold Formula.eval
  dsimp
  unfold Formula.evalSome
  apply h

  theorem intro {T T' : Type} (f : T → Formula T'):
    Formula.var Shared.quant.some (f) →
    (∃ x, f x) := by
  intro h
  unfold Formula.eval at h
  dsimp at h
  unfold Formula.evalSome at h
  apply h
end Some

def F9 := Formula.var Shared.quant.some (
  fun (t : ∷ Time) => (
    Formula.var Shared.quant.all (
      fun (n : ∷ Node) => (
                    Formula.prop ((t ≡ n))
      )
    )
  )
)
#print F9
lemma l9 (t : ∷ Time) : (F9 Time Node) := by
  unfold F9
  apply Some.elim
  exists t
  apply All.intro; intro n
  unfold Formula.eval
  sorry

#check Exists
variable (t : ∷ Time)
lemma l9' (h : F9 Time Node) : ∃ (t : ∷ Time), ∀ (n : ∷ Node), t ≡ n := by
  apply Some.intro at h
  match h with
  | ⟨t, h⟩ =>
    apply (All.elim) at h
    apply Exists.intro t
    unfold Formula.eval at h
    apply h

/- freie Variablen -/
#print pred2
def F10 := Formula.var Shared.quant.all (
      fun (n : ∷ Node) => (
                    Formula.prop (pred2 Time Node n t)
      )
    )
#check F10
def F11 := Formula.var Shared.quant.some (
  fun (t : ∷ Time) => (
      Formula.prop ((F10 Time Node t) ∧ (t + t ≡ t))
  )
)
#print F11
lemma l11 : (F11 Time Node) := by
  unfold F11
  unfold F10
  sorry
