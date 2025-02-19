/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.RelType
-- import ThoR.Relation.RelTypeCons

namespace ThoR

-- TODO move mult_to_pred to ThoR.Set
def mult_to_pred {R : Type u} [ThoR.TupleSet R] (m : Shared.mult) : R → Prop :=
  match m with
  | Shared.mult.set  => λ _ => True
  | Shared.mult.some => ThoR.SetMultPredicates.some
  | Shared.mult.lone => ThoR.SetMultPredicates.lone
  | Shared.mult.one  => ThoR.SetMultPredicates.one

namespace HasRelType

inductive hasType' {R: Type} [TupleSet R]: R → (RelType' R) → Type :=
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
    (t1 : RelType' R) (m1 m2 : Shared.mult) (t2 : RelType' R)
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
      hasType' r' (RelType'.complex t1 m1 m2 t2)
  -- r1' & r2' : t1 & t2
  | intersect (n : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' & r2') (RelType'.intersect t1 t2)
  -- r1' + r2' : t1 + t2
  | add (n : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' + r2') (RelType'.add t1 t2)
  -- r1' - r2' : t1 - t2
  | sub (n : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R),
    hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' - r2') (RelType'.sub t1 t2)
  -- r1' ++ r2' : t1 ++ t2
  | append (n : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' ++ r2') (RelType'.append t1 t2)
  -- TODO cartprod redundant to complex
  -- r1' ⟶ r2' : t1 ⟶ t2
  | cartprod (n1 n2 : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' ⟶ r2') (RelType'.cartprod t1 t2)
  -- r1' ⋈ r2' : t1 ⋈ t2
  | dotjoin (n1 n2 : ℕ) (t1 : RelType' R) (t2 : RelType' R) :
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' ⋈ r2') (RelType'.dotjoin t1 t2)
  -- ^r' : ^t
  | transclos (t : RelType' R):
    ∀ (r' : R), hasType' r' t
    → hasType' (^r') (RelType'.transclos t)
  -- *r' : *t
  | reftransclos (t : RelType' R):
    ∀ (r' : R), hasType' r' t
    → hasType' (^r') (RelType'.reftransclos t)
  -- -- ~r' : ~t
  -- | transpose (t : RelType R 2):
  | transpose (t : RelType' R):
    ∀ (r' : R), hasType' r' t
    → hasType' (~ r') (RelType'.transpose t)
  -- r1' <: r2' : t1 <: t2
  | domrestr (n : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' <: r2') (RelType'.domrestr t1 t2)
  -- -- r1' :> r2' : t1 :> t2
  | rangerestr (n : ℕ) (t1 : RelType' R) (t2 : RelType' R):
    ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
    → hasType' (r1' <: r2') (RelType'.rangerestr t1 t2)


local macro "checkArityEqN" "(" t1:term ", " t2:term ", " n:term ")": term =>
`(do
    let n1 ← ($t1).arity
    let n2 ← ($t2).arity
    if (n1 = $n) /\ (n2 = $n)
    then return $n
    else none)

local macro "checkArityN" "(" t:term ", " n:term ")": term =>
`(do
    let tn ← ($t).arity
    if (tn = $n)
    then return $n
    else none)

local macro "checkArityNNN" "(" t1:term ", " n1:term ", " t2:term ", " n2:term ", " n:term ")": term =>
`(do
    let tn1 ← ($t1).arity
    let tn2 ← ($t2).arity
    if (tn1 = $n1) /\ (tn2 = $n2)
    then return $n
    else none)

def hasType'.arity {R: Type} [TupleSet R] {r : R} {t : RelType' R} (h : hasType' r t):=
  match h with
  | sig _ _ _ _ => some 1
  | unary_rel _ _ _ _ _ _ => some 1
  | rel _ n _ _ _ => some n
  | constant _ n _ _ _ => some n
  | complex n1 n2 t1 _ _ t2 _ _ _ _ _ _ _ _ _ _ =>
      do
        let nt1 ← t1.arity
        let nt2 ← t2.arity
        if nt1 = n1 /\ nt2 = n2
        then return n1 + n2
        else none
  | intersect n t1 t2 _ _ _ _ => checkArityEqN (t1, t2, n)
  | add n t1 t2 _ _ _ _ => checkArityEqN (t1, t2, n)
  | sub n t1 t2 _ _ _ _ => checkArityEqN (t1, t2, n)
  | append n t1 t2 _ _ _ _ => checkArityEqN (t1, t2, n)
  | cartprod n1 n2 t1 t2 _ _ _ _ =>
          do
            let nt1 ← t1.arity
            let nt2 ← t2.arity
            if (nt1 = n1) /\ (nt2 = n2)
            then return n1 + n2
            else none
  | dotjoin n1 n2 t1 t2 _ _ _ _ =>
          do
            let nt1 ← t1.arity
            let nt2 ← t2.arity
            if (nt1 = n1+1) /\ (nt2 = n2+1)
            then return n1 + n2
            else none
  | transclos t _ _ => checkArityN(t, 2)
  | reftransclos t _ _ => checkArityN(t, 2)
  | transpose t _ _ => checkArityN(t, 2)
  | domrestr n t1 t2 _ _ _ _ => checkArityNNN(t1, 1, t2, n, n)
  | rangerestr n t1 t2 _ _ _ _ => checkArityNNN(t1, n, t2, 1, n)

  def hasType {R: Type} [TupleSet R] {n : ℕ} (r : R) (t : RelType R n)
    := ∃ ht : hasType' r t.1, ht.arity = some n

end HasRelType

infixl:63 " ∷ " => HasRelType.hasType
-- variable (R : Type) [TupleSet R] (s : R) (h : HasArity.hasArity s 1)
namespace HasRelType
  variable (R : Type) [TupleSet R]
  namespace sig
    lemma isUnary (a : R) (m : Shared.mult):
      a ∷ RelType.sig R m → HasArity.hasArity a 1
    := by sorry
  end sig
  namespace TupleSet
    lemma refl (R : Type) [TupleSet R] (a : R) (m : Shared.mult):
      (h1 : HasArity.hasArity a 1) → mult_to_pred m a
      → a ∷ RelType.unary_rel R m a h1 := by
      -- intro h1 h2
      -- constructor <;> try simp
      -- TODO inversion properties for arity axioms in TupleSet
      sorry
  end TupleSet
end HasRelType

end ThoR
