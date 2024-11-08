/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Relation.TupleSet

open ThoR
open ThoR.Set
open ThoR.TupleSet₀
open ThoR.HasCard
open ThoR.SetMultPredicates
open ThoR.HasArity
open ThoR.RelConstants
section

variable (R: Type u) [TupleSet₀ R]

lemma arity_iden {R : Type} [TupleSet R]:
  HasArity.hasArity (@RelConstants.iden R _) 2 := by sorry

lemma arity_univ {R : Type} [TupleSet R]: HasArity.hasArity (@RelConstants.univ R _) 1 := by
  apply TupleSet₀.arity_1
  apply Set.subset_refl

-- lemma add_arity_left (r1 r2 : R) [TupleSet R]:
--   Arity.arity r1 = Arity.arity r2 → Arity.arity (r1 + r2) = Arity.arity r1 := by sorry

lemma subset_hasArity {R: Type u} [TupleSet₀ R] {r1 r2 : R} {n : ℕ} :
  hasArity r2 n → r1 ⊂ r2 → hasArity r1 n := by sorry

lemma union_hasArity (r1 r2 : R) (n : ℕ) :
  hasArity r1 n → hasArity r2 n → hasArity (r1 + r2) n := by sorry

-- cartprod_rel0_l defines () uniquely
lemma rel0_uniq (rel0' : R):
  -- TODO adjust precedence levels such that the parentheses in
  --      (r ⟶ rel0') = r are not necessary
  (∀ r : R, (r ⟶ rel0') = r) → rel0' = () := by
  intro H0
  have H1: (() ⟶ rel0') = () := by
    apply H0
  have H2: (() ⟶ rel0') = rel0' := by
    apply cartprod_rel0_l
  rw [← H1, H2]

-- set_option pp.all true

-- ein endliches r : R mit hasArity 1
-- kann als Vereinigung von singletons (mit hasArity 1) dargestellt werden
-- Konsequenz des inv-Lemma zur Definition von card
lemma finset_enum (r : R) (n : ℕ):
  r ⊂ univ → hasCard r n →
  -- e is a duplicate-free list of unary singletons
  ∃ e : List { x : R | x ⊂ univ ∧ one x},
    List.Nodup e
    ∧
    -- r is the union of all elements of e
    r = List.foldl (λ acc x : R => acc + x) SetConstants.none e
    := by sorry

def fin_rel := { r : R | ∃ n : ℕ, hasCard r n }
def fin_scalar := { r : fin_rel R | hasArity r.1 1 }
def singleton := {r : R | one r ∧ hasArity r 1 }
def bin_rel := { r : R | hasArity r 2}
def is_total (r : bin_rel R) := True
def total_order := { r : bin_rel R | is_total R r}

-- Korollar zu finset_enum = Auswahlaxiom für endliche Mengen
lemma axiom_of_choice (r : fin_scalar R):
  some r.1.1 →
  ∃ (start : singleton R) -- minimales Element start
    (next : bin_rel R),   -- totale Ordnung next
    (is_total R next) →
    r.1 = start.1 + (start.1 ⋈ ^next.1) := by sorry

-- Spezialfall der Noether-Induktion
lemma noether_induction (r : fin_scalar R) (P : R -> Prop)
  (start : singleton R) (next : bin_rel R):
    r.1 = start.1 + (start.1 ⋈ ^next.1) →
    P start.1 →
    forall x : R, one x → x ⊂ r → (P x → P (x ⋈ next)) →
    forall x : R, one x → x ⊂ r → P x
    := by sorry

-- mit noether_induction sollte sich z.B. Assoziativität des dotjoin
-- für endliche Relationen (mit geeigneten Aritäts-Beschränkungen)
-- zeigen lassen -- und zwar durch Lifting des Lemmas
-- zum "punktweisen" dotjoin (s. Masterprojektbericht A. Mayer)
-- (Lifting = Anwendung von noether_induction)

-- r . iden = r
lemma dotjoin_neutral_r (r : R) [TupleSet₀ R]: iden ⋈ r = r := by sorry
lemma dotjoin_neutral_l (r : R) [TupleSet₀ R]: r ⋈ iden = r := by sorry
-- iden . iden = iden
lemma iden_idem (R : Type u) [TupleSet₀ R]: (@iden R _) ⋈ (iden) = (iden) := by
  rw [dotjoin_neutral_r]

end
