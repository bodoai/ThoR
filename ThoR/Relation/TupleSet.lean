/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Relation.Notation
import ThoR.Relation.Set

open ThoR
open ThoR.Set
namespace ThoR

-- FIXME: Präzedenzen der Operatoren mit Lean.Notation abgleichen

class TupleSet₀ (R : Type u) extends
  Set R, Cartprod R, Dotjoin R,
  Transclos R, ReflTransclos R, Transpose R,
  Append R, DomRestr R, RangeRestr R,
  HasArity R, RelConstants R
  where
  /-- inference rules -/
  -- rel0
  rel₀_elim : ∀ r : R, r ⊂ () → r ⟶ r = r
  rel₀_intro : ∀ r : R, (r ⟶ r) = r → r ⊂ ()
  rel₀_inv : ∀ r : R, r ⊂ rel₀ → r = SetConstants.none ∨ r = ()
  -- univ
  univ1 : ∀ p q : R, (p ⟶ q) ⊂ univ → p & q = SetConstants.none
  univ2 : (univ ⟶ univ) & univ = SetConstants.none
  univ3 : ∀ p q : R, (p ⟶ q) ⊂ univ → p + q ⊂ univ + ()
  univ4 : univ & rel₀ = SetConstants.none
  -- iden
  iden_elim : ∀ r : R, r ⊂ iden -> ∃ x : R, x ⊂ univ /\ r ⊂ (univ ⟶ univ)
  iden_intro : ∀ x : R, x ⊂ univ -> (x ⟶ x) ⊂ iden
  -- cartesian product
  cartprod_subset : ∀ p p' q' q : R,
    p ⊂ p' → q ⊂ q' → (p ⟶ q) ⊂ (p' ⟶ q')
  cartprod_proj1: ∀ p p' q : R,
    (p ⟶ q) ⊂ (p' ⟶ q) → p ⊂ p'
  cartprod_proj2: ∀ p q' q : R,
    (p ⟶ q) ⊂ (p ⟶ q') → q ⊂ q'
  cartprod_rel0_l : ∀ r : R, (() ⟶ r) = r
  cartprod_rel0_r : ∀ r : R, (r ⟶ ()) = r
  cartprod_none_l : ∀ r : R, (SetConstants.none ⟶ r) = SetConstants.none
  cartprod_none_r : ∀ r : R, (r ⟶ SetConstants.none) = SetConstants.none
  cartprod_assoc : ∀ p q r : R,
    (p ⟶ (q ⟶ r)) = ((p ⟶ q) ⟶ r)
  -- TODO Distributiv-Gesetze ableitbar?
  cartprod_distr_union_l : ∀ p q r : R,
    ((p + q) ⟶ r) = (p ⟶ r) + (q ⟶ r)
  cartprod_distr_union_r : ∀ p q r : R,
    (p ⟶ (q + r)) = (p ⟶ q) + (p ⟶ r)
  -- dotjoin
  dotjoin_put : ∀ k v a r : R,
    k ⊂ univ → one k → (k ⟶ v) ⊂ r →
    (a ⟶ v) ⊂ ((a ⟶ k) ⋈ r)
  dotjoin_get : ∀ k v a r : R,
    k ⊂ univ → one k -> (a ⟶ v) ⊂ ((a ⟶ k) ⋈ r) →
    (k ⟶ v) ⊂ r
  -- transclos
  transclos_1 : ∀ a b r : R,
    (a ⟶ b) ⊂ r → (a ⟶ b) ⊂ (^r)
  transclos_n : ∀ a b c r : R,
    (a ⟶ b) ⊂ (^r) →
    (b ⟶ c) ⊂ (^r) ->
    (a ⟶ c) ⊂ (^r)
  /-- TODO: Minimal-Eigenschaft des trans. Abschluss -/
  -- arity
  arity_0 : hasArity rel₀ 0
  arity_1 : ∀ r : R, r ⊂ univ → hasArity r 1
  arity_n : ∀ (p q : R) (n : ℕ),
    hasArity p n → hasArity q m → hasArity (p ⟶ q) (n + m)
  -- TODO inversion property for arity?
  -- TODO Prüfen, ob es nicht geschickter ist, arity, transclos etc.
  --      als induktive Prop-Types zu definieren
  arity_none : ∀ (n : ℕ), hasArity none n

class TupleSet (R : Type u) extends TupleSet₀ R, Card R-- , Arity R

--variable (R : Type u) [TupleSet R]

end ThoR
