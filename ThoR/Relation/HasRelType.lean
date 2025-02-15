/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.RelType
-- import ThoR.Relation.RelTypeCons

namespace ThoR

def mult_to_pred {R : Type u} [ThoR.TupleSet R] (m : Shared.mult) : R → Prop :=
  match m with
  | Shared.mult.set  => λ _ => True
  | Shared.mult.some => ThoR.SetMultPredicates.some
  | Shared.mult.lone => ThoR.SetMultPredicates.lone
  | Shared.mult.one  => ThoR.SetMultPredicates.one

namespace HasRelType

inductive hasType' {R: Type} [TupleSet R]: R → (RelType' R) → Prop :=
  -- subset : m univ
  | sig (m : Shared.mult):
    ∀ (subset : R), subset ⊂ RelConstants.univ → mult_to_pred m subset
    → hasType' subset (RelType.sig R m)
  -- subet : m superset
  | unary_rel (m : Shared.mult) (superset : R) (h : HasArity.hasArity superset 1):
    ∀ (subset : R), subset ⊂ superset → mult_to_pred m subset
    → hasType' subset (RelType.unary_rel R m superset h)
  -- subrel : subrel
  | rel (superrel : R) (n : ℕ) (h: HasArity.hasArity superrel n):
    ∀ (subrel : R), subrel ⊂ superrel
    → hasType' subrel (RelType.rel R superrel n h)
  -- none ∷ constant none, univ ∷ constant univ, id ∷ constant id
  | constant (c : R) (n : ℕ) (h : HasArity.hasArity c n):
    ∀ (c' : R), c' = c
    → hasType' c' (RelType.constant R c n h)
  -- r1' ∷ t1 , r2' ∷ t2 → t1 m1 ⟶ m2 t2
  -- TODO replace ⋈ by correct operator "⋈*" (left/right)
  | complex
    (n1 n2 : ℕ)
    (r : R) (ha: HasArity.hasArity r (n1 + n2))
    (t1 : RelType R n1) (m1 m2 : Shared.mult) (t2 : RelType R n2)
     :
    ∀ (r1' r2' : R),
      hasType' r1' t1 → hasType' r2' t2 →
      ∀ (r' : R),
        (r' ⊂ r1' ⟶ r2') →
      (
        (∀ (r1'' : R),
          r1'' ⊂ r1' → SetMultPredicates.one r1'' → (mult_to_pred m2 (r1'' ⋈ r')))
      ) →
      (
        (∀ (r1'' : R),
          r1'' ⊂ r1' → SetMultPredicates.one r1'' → (hasType' (r1'' ⋈ r') t2))
      )
        →
      (
        (∀ (r2'' : R),
          r2'' ⊂ r2' → SetMultPredicates.one r2'' → (mult_to_pred m1 (r' ⋈ r2'')))
      )
        →
      (
        (∀ (r2'' : R),
          r2'' ⊂ r2' → SetMultPredicates.one r2'' → (hasType' (r' ⋈ r2'') t1))
      )
       →
      hasType' r' t
  -- r1' & r2' : t1 & t2
  | intersect (n : ℕ) (t1 : RelType R n) (t2 : RelType R n):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' & r2') (t1 & t2)
  -- -- r1' + r2' : t1 + t2
  -- | add (n : ℕ) (t1 : RelType R n) (t2 : RelType R n):
  --   ∀ (r1' r2' : R), hasType r1' t1 → hasType r2' t2
  --   → hasType (r1' + r2') (t1 + t2)
  -- -- r1' - r2' : t1 - t2
  -- | sub (n : ℕ) (t1 : RelType R n) (t2 : RelType R n):
  --   ∀ (r1' r2' : R),
  --   hasType r1' t1 → hasType r2' t2
  --   → hasType (r1' - r2') (t1 - t2)
  -- -- r1' ++ r2' : t1 ++ t2
  -- | append (n : ℕ) (t1 : RelType R n) (t2 : RelType R n):
  --   ∀ (r1' r2' : R), hasType r1' t1 → hasType r2' t2
  --   → hasType (r1' ++ r2') (t1 ++ t2)
  -- -- TODO cartprod redundant to complex
  -- -- r1' ⟶ r2' : t1 ⟶ t2
  -- | cartprod (n1 n2 : ℕ) (ha : n=n1+n2) (t1 : RelType R n1) (t2 : RelType R n2) (ht : t=ha ▸ ((RelType.cartprod t1 t2))):
  --   ∀ (r1' r2' : R),
  --     hasType r1' t1 → hasType r2' t2 →
  --     ∀ (r' : R),
  --       (r' ⊂ r1' ⟶ r2')
  --     → hasType r' t
  -- r1' ⋈ r2' : t1 ⋈ t2
  | dotjoin (n1 n2 : ℕ) (t1 : RelType R (n1+1)) (t2 : RelType R (n2+1)) :
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' ⋈ r2') (t1 ⋈ t2)
  -- -- ^r' : ^t
  -- | transclos (t : RelType R 2):
  --   ∀ (r' : R), hasType r' t
  --   → hasType (^r') (^t)
  -- -- *r' : *t
  -- | reftransclos (t : RelType R 2):
  --   ∀ (r' : R), hasType r' t
  --   → hasType (*r') (*t)
  -- -- ~r' : ~t
  -- | transpose (t : RelType R 2):
  --   ∀ (r' : R), hasType r' t
  --   → hasType (~ r') (~ t)
  -- -- r1' <: r2' : t1 <: t2
  -- | domrestr (n : ℕ) (t1 : RelType R 1) (t2 : RelType R n):
  --   ∀ (r1' r2' : R), hasType r1' t1 → hasType r2' t2
  --   → hasType (r1' <: r2') (RelType.domrestr t1 t2)
  -- -- r1' :> r2' : t1 :> t2
  -- | rangerestr (n : ℕ) (t1 : RelType R n) (t2 : RelType R 1):
  --   ∀ (r1' r2' : R), hasType r1' t1 → hasType r2' t2
  --   → hasType (r1' :> r2') (RelType.rangerestr t1 t2)

infixl:63 " ∷ " => hasType'

def hasType'.checkArity {R: Type} [TupleSet R]: R → (RelType R n) :=
  match t with
  | RelType'.sig _    => some 1
  | unary_rel _ _ _   => some 1
  | rel _ n _         => some n
  | constant _ n _    => some n
  | complex t1 _ _ t2 => do
                          let n1 ← t1.arity
                          let n2 ← t2.arity
                          some (n1+n2)
  | intersect t1 t2   => do
                          let n1 ← arity t1
                          let n2 ← arity t2
                          if (n1 = n2)
                          then return n1
                          else none
  | dotjoin t1 t2 => do
                      let n1 ← t1.arity
                      let n2 ← t2.arity
                      if (n1 > 0 ∧ n2 >0)
                      then return n1 + n2 - 2
                      else none



  theorem arity {R : Type} [TupleSet R] (n : ℕ) (r : R) (t : RelType R n):
    r ∷ t → HasArity.hasArity r n := by
    intros ht
    sorry
    -- cases ht with
    -- -- sig m r h1 hs hm
    -- | sig m r' h1 h2 h3 h4 => -- WTF wird h2 verschluckt?
    --   apply (subset_hasArity h1 h3)
    -- | TupleSet r' h1 h2 h3 =>
    --   apply (subset_hasArity h1 h3) -- WTF wird h2 verschluckt?

    theorem intersect_consistent {R : Type} [TupleSet R] {n : ℕ}
      {r1 r2 : R} {t1 t2 : RelType R n}:
      r1 ∷ t1 → r2 ∷ t2 → r1 & r2 ∷ RelType.intersect t1 t2 := by sorry

    theorem add_consistent {R : Type} [TupleSet R] {n : ℕ}
      {r1 r2 : R} {t1 t2 : RelType R n}:
      r1 ∷ t1 → r2 ∷ t2 → r1 + r2 ∷ RelType.add t1 t2 := by sorry

    theorem sub_consistent {R : Type} [TupleSet R] {n : ℕ}
      {r1 r2 : R} {t1 t2 : RelType R n}:
      r1 ∷ t1 → r2 ∷ t2 → r1 - r2 ∷ RelType.sub t1 t2 := by sorry

    theorem append_consistent {R : Type} [TupleSet R] {n : ℕ}
      {r1 r2 : R} {t1 t2 : RelType R n}:
      r1 ∷ t1 → r2 ∷ t2 → r1 ++ r2 ∷ RelType.append t1 t2 := by sorry

    theorem cartprod_consistent {R : Type} [TupleSet R] {n1 n2 : ℕ}
      {r1 r2 : R} {t1 : RelType R n1} {t2 : RelType R n2}:
      r1 ∷ t1 → r2 ∷ t2 → r1 ⟶ r2 ∷ RelType.cartprod t1 t2 := by sorry

    theorem dotjoin_consistent {R : Type} [TupleSet R] {n1 n2 : ℕ}
      {r1 r2 : R} {t1 : RelType R (n1+1)} {t2 : RelType R (n2+1)}:
      r1 ∷ t1 → r2 ∷ t2 → r1 ⋈ r2 ∷ RelType.dotjoin t1 t2 := by sorry

    theorem transclos_consistent {R : Type} [TupleSet R]
      {r : R} {t : RelType R 2}:
      r ∷ t → ^r ∷ RelType.transclos t := by sorry

    theorem reftransclos_consistent {R : Type} [TupleSet R]
      {r : R} {t : RelType R 2}:
      r ∷ t → *r ∷ RelType.reftransclos t := by sorry

    theorem transpose_consistent {R : Type} [TupleSet R]
      {r : R} {t : RelType R 2}:
      r ∷ t → ~ r ∷ RelType.transpose t := by sorry

    theorem domrestr_consistent {R : Type} [TupleSet R] {n : ℕ}
      {r1 r2 : R} {t1 : RelType R 1} {t2 : RelType R n}:
      r1 ∷ t1 → r2 ∷ t2 → r1 <: r2  ∷ RelType.domrestr t1 t2 := by sorry

    theorem rangerestr_consistent {R : Type} [TupleSet R] {n : ℕ}
      {r1 r2 : R} {t1 : RelType R n} {t2 : RelType R 1}:
      r1 ∷ t1 → r2 ∷ t2 → r1 :> r2  ∷ RelType.rangerestr t1 t2 := by sorry

end HasRelType

-- variable (R : Type) [TupleSet R] (s : R) (h : HasArity.hasArity s 1)
namespace HasRelType
  variable (R : Type) [TupleSet R]
  namespace sig
    lemma isUnary (a : R) (m : Shared.mult):
      a ∷ RelType.sig m (Eq.refl 1) → HasArity.hasArity a 1
    := by sorry
  end sig
  namespace TupleSet
    lemma refl (R : Type) [TupleSet R] (a : R) (m : Shared.mult):
      (h1 : HasArity.hasArity a 1) → mult_to_pred m a
      → a ∷ RelType.unary_rel m a (Eq.refl 1) h1 := by
      -- intro h1 h2
      -- constructor <;> try simp
      -- TODO inversion properties for arity axioms in TupleSet
      sorry
  end TupleSet
end HasRelType

end ThoR
