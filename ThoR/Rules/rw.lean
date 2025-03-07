import ThoR

namespace lift
  open ThoR

  /- predicates -/
  lemma subset (R : Type) [TupleSet R] {n : ℕ} {t1 t2 : RelType R n} {a : Rel t1} {b : Rel t2} : a.relation ⊂ b.relation ↔ a ⊂ b := by
    dsimp [HSubset.hSubset]
    dsimp [Rel.subset]
    trivial

  lemma subset' (R : Type) [TupleSet R] {n : ℕ} {t1 t2 : RelType R n} {a : Rel t1} {b : Rel t2} : Subset.subset a.relation b.relation ↔ a ⊂ b := by
    dsimp [HSubset.hSubset]
    dsimp [Rel.subset]
    trivial

  lemma equal (R : Type) [TupleSet R] {n : ℕ} {t1 t2 : RelType R n} {a : Rel t1} {b : Rel t2} : a.relation = b.relation ↔ a ≡ b := by
    dsimp [HEqual.hEqual]
    trivial

  lemma nEqual (R : Type) [TupleSet R] {n : ℕ} {t1 t2 : RelType R n} {a : Rel t1} {b : Rel t2} : a.relation ≠ b.relation ↔ a ≢ b := by
    dsimp [HEqual.hEqual]
    trivial

  lemma mult.no (R : Type) [TupleSet R] {n : ℕ} {t : RelType R n} {a : Rel t} : SetMultPredicates.no a.relation ↔ SetMultPredicates.no a := by
    simp [SetMultPredicates.no]
  lemma mult.lone (R : Type) [TupleSet R] {n : ℕ} {t : RelType R n} {a : Rel t} : SetMultPredicates.lone a.relation ↔ SetMultPredicates.lone a := by
    simp [SetMultPredicates.lone]
  lemma mult.one (R : Type) [TupleSet R] {n : ℕ} {t : RelType R n} {a : Rel t} : SetMultPredicates.one a.relation ↔ SetMultPredicates.one a := by
    simp [SetMultPredicates.one]
  lemma mult.some (R : Type) [TupleSet R] {n : ℕ} {t : RelType R n} {a : Rel t} : SetMultPredicates.some a.relation ↔ SetMultPredicates.some a := by
    simp [SetMultPredicates.some]

  /- binary operators -/
  -- TODO to be completed
  lemma add (R : Type) [TupleSet R] {n : ℕ} {t1 t2 : RelType R n} {a : Rel t1} {b : Rel t2} : a.relation + b.relation = (a + b).relation := by
    dsimp [HAdd.hAdd]

  lemma add' (R : Type) [TupleSet R] {n : ℕ} {t1 t2 : RelType R n} {a : Rel t1} {b : Rel t2} : Add.add a.relation b.relation = (a + b).relation := by
    dsimp [HAdd.hAdd]

  lemma dotjoin (R : Type) [TupleSet R] {n1 n2 : ℕ} {t1 : RelType R (n1 + 1)} {t2 : RelType R (n2 + 1)} {a : Rel t1} {b : Rel t2} : a.relation ⋈ b.relation = (a ⋈ b).relation := by
    dsimp [HDotjoin.hDotjoin]

  /- unary operators -/
  -- TODO to be completed
  lemma transclos (R : Type) [TupleSet R] {t : RelType R 2} {a : Rel t} : ^ a.relation = (^ a).relation := by
    dsimp [HTransclos.hTransclos]

end lift

syntax " thor_lift_pred " " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_lift_pred at $hyp) => `(tactic|
  first
    | rw [← lift.equal] at $hyp
    | rw [← lift.nEqual] at $hyp
    | rw [← lift.subset] at $hyp
    | rw [← lift.mult.no] at $hyp
    | rw [← lift.mult.lone] at $hyp
    | rw [← lift.mult.one] at $hyp
    | rw [← lift.mult.some] at $hyp
)

syntax " thor_lift_op " " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_lift_op at $hyp) => `(tactic|
  repeat
    first
      | rw [← lift.dotjoin] at $hyp
      | rw [← lift.add] at $hyp
)

syntax " thor_lift " " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_lift at $hyp) => `(tactic|
  thor_lift_pred at $hyp
  ;
  thor_lift_op at $hyp
)

syntax " thor_unlift_pred " " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_unlift_pred at $hyp) => `(tactic|
  first
    | rw [lift.equal] at $hyp
    | rw [lift.nEqual] at $hyp
    | rw [lift.subset] at $hyp
    | rw [lift.mult.no] at $hyp
    | rw [lift.mult.lone] at $hyp
    | rw [lift.mult.one] at $hyp
    | rw [lift.mult.some] at $hyp
)

syntax " thor_unlift_op " " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_unlift_op at $hyp) => `(tactic|
  repeat
    first
      | rw [lift.dotjoin] at $hyp
      | rw [lift.add] at $hyp
)

syntax " thor_unlift " " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_unlift at $hyp) => `(tactic|
  thor_unlift_op at $hyp
  ;
  thor_unlift_pred at $hyp
)

syntax " thor_rw " "[" Lean.Parser.Tactic.rwRule "]" " at " Lean.Parser.Tactic.locationHyp : tactic
macro_rules
| `(tactic| thor_rw [$rw_rule] at $hyp) => `(tactic|
  thor_lift at $hyp
  ;
  rw [$rw_rule] at $hyp
  ;
  thor_unlift at $hyp
)
