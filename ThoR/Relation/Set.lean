/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Relation.Notation

namespace ThoR

class SetMultPredicates (α : Type u) where
  no   : α -> Prop
  lone : α -> Prop
  one  : α -> Prop
  some : α -> Prop

/--
  `Set` models the concept "set with cardinality" as algebraic structure.
-/
class Set (R : Type u) extends
  Subset R,             -- subset predicate `⊂`
  Intersect R,          -- intersection operator `&`
  Add R,                -- union operator `+`
  Sub R,                -- set difference `-`
  HasCard R,            -- cardinality predicate
  SetConstants R,       -- empty set
  SetMultPredicates R,   -- set multiplicity predicates `no`, `lone`, `one`, `some`
  IfThenElse R
  where
  /-- inference rules --/
  -- subset
  subset_intro : ∀ a b : R,
    (∀ c : R, c ⊂ a → c ⊂ b) → a ⊂ b
  subset_refl : ∀ a : R, a ⊂ a
  subset_trans : ∀ a b c : R,
    a ⊂ b → b ⊂ c → a ⊂ c
  subset_antisym : ∀ (a b : R),
    a ⊂ b → b ⊂ a → a = b
  -- intersect
  intersect_intro : ∀ a b c : R,
    c ⊂ a → c ⊂ b → c ⊂ a & b  -- c in a → c in b → c in a & b
  intersect_eliml : ∀ a b : R, a & b ⊂ a -- a & b in a
  intersect_elimr : ∀ a b : R, a & b ⊂ b -- a & b in b
  -- union
  union_introl : ∀ a b : R, a ⊂ a + b
  union_intror : ∀ a b : R, b ⊂ a + b
  union_elim: ∀ a b c : R,
    a ⊂ c → b ⊂ c → a + b ⊂ c
  -- none
  none_intro: ∀ a : R, none ⊂ a
  -- diff
  diff_intro : forall a b : R,
    a & b = none → a - b = a
  diff_elim : forall a b : R,
    (a & b) & (a - b) = none
  bottom_elim : forall a : R, a - none = a
  diff_diff_elim : ∀ a b : R,
    a - (a - b) = a & b
  -- quant. predicates
  no_intro : ∀ a : R, a = none → no a
  no_elim : ∀ a : R, no a → a = none
  some_intro : ∀ a : R, ¬ no a -> some a
  some_elim : ∀ a : R, some a → ¬ no a
  one_intro : ∀ a : R,
    some a → (∀ x : R, some x → x ⊂ a → x = a) → one a
  one_elim_some : ∀ a : R,
    one a → some a
  one_elim_uniq:
    one a → (∀ x : R, some x → x ⊂ a → x = a)
  lone_intro_no : ∀ a : R, no a → lone a
  lone_intro_one : ∀ a : R, one a → lone a
  lone_elim : ∀ a : R, lone a → no a ∨ one a
  -- cardinality --
  card₀ : hasCard none 0
  card_one : ∀ a : R, one a → hasCard a 1
  card_n : ∀ (a b : R) (n : ℕ),
    hasCard a n → one b → no (a & b) → hasCard (a + b) (n + 1)
  -- TODO geeignetes inv-Lemma zur Definition von hasCard
  card_uniq : ∀ (a : R) (n m : ℕ),
    hasCard a n → hasCard a m → n = m
  if_then : ∀ (p : Prop) (a b : R),
    p → IfThenElse.ifThenElse p a b = a
  if_else : ∀ (p : Prop) (a b : R),
    ¬ p → IfThenElse.ifThenElse p a b = b

end ThoR
