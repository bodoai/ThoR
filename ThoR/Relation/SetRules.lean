/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Relation.Set

open ThoR
open ThoR.Set
open ThoR.HasCard
section

variable (R: Type u) [ThoR.Set R]

lemma union_comm (a b : R):
  (a + b) = (b + a) := by
  apply subset_antisym
  . apply union_elim
    apply union_intror
    apply union_introl
  . apply union_elim
    apply union_intror
    apply union_introl

lemma eq_subset (a b : R): a = b → a ⊂ b := by
  intro Heq
  rw [Heq]
  apply Set.subset_refl

lemma card_some (a : R) (n : ℕ):
  hasCard a n → n > 0 → SetMultPredicates.some a := by
  intro Hc Hn
  apply some_intro
  intro contra
  have contra' : a = SetConstants.none := by
    apply no_elim
    exact contra
  rw [contra'] at Hc
  have Hcn : hasCard SetConstants.none 0 := by
    apply @card₀.{u} R
  have Hn_contra : n = 0 := by
    eapply @card_uniq.{u} R
    apply Hc
    apply Hcn
  rw [Hn_contra] at Hn
  simp at Hn

lemma union_subset_r (a b b' : R):
  b ⊂ b' → (a + b) ⊂ (a + b') := by
    intro Hbb'
    have H1: a ⊂ a + b' := by
      apply union_introl
    have H2: b' ⊂ a + b' := by
      apply union_intror
    have H3 : b ⊂ a + b' := by
      eapply Set.subset_trans
      apply Hbb'
      apply H2
    apply union_elim
    . apply H1
    . apply H3

  lemma union_id: ∀ a : R, a + a = a := by
    intro a
    apply Set.subset_antisym
    . apply union_elim; repeat apply Set.subset_refl
    . apply union_introl

  lemma intersect_id: ∀ a : R, a & a = a := by
    intro a
    apply subset_antisym
    . apply intersect_eliml
    . apply intersect_intro; repeat apply Set.subset_refl

  lemma  SetConstants.none_intersect : ∀ a : R, a & SetConstants.none = SetConstants.none := by
    intro a
    apply subset_antisym
    . apply intersect_elimr
    . apply intersect_intro; repeat apply Set.none_intro

  lemma  SetConstants.none_union : ∀ a : R, a + SetConstants.none = a := by
    intro a
    apply subset_antisym
    . apply union_elim
      apply Set.subset_refl
      apply Set.none_intro
    . apply union_introl

  lemma SetConstants.none_uniq (none' : R) :
    (∀ a : R, none' ⊂ a) → none' = SetConstants.none := by
    intro Hn'
    apply subset_antisym
    . apply Hn'
    . apply Set.none_intro

-- ein endliches r : R kann als Vereinigung von singletons dargestellt werden
-- Konsequenz des inv-Lemma zur Definition von card
lemma finset_enum (r : R) (n : ℕ):
  hasCard r n →
  -- e is a duplicate-free list of singletons
  ∃ e : List { x : R | SetMultPredicates.one x },
    List.Nodup e
    ∧
    -- r is the union of all elements of e
    r = List.foldl (λ acc x : R => acc + x) SetConstants.none e
    := by sorry

end
