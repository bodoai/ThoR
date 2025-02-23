/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Relation.Notation
import ThoR.Relation.TupleSetRules
import ThoR.Shared.Syntax.multType

-- FIXME: Präzedenzen der Operatoren mit Lean.Notation abgleichen
-- FIXME: eigene Datei für die Definition aller Operator-Typ-Klassen
namespace ThoR

inductive Rel'.mult where | no | lone | one | some

-- TODO sub type relation: t1 ⊑ t2
--      true -> (∀ (r ∷ t1), (r ∷ t2)) → t1 ⊑ t2
--      test stub: true -> t1 = t2
mutual
  inductive RelType' : Type :=
    -- sig a {...}
    | sig (m : Rel'.mult) : RelType'
    -- a : <mult> r
    | unary_rel (r : Rel') (m : Rel'.mult) : RelType'
    -- a : r
    | rel (r : Rel') (n : ℕ): RelType'
    -- none : none, univ : univ, id : id
    | constant (r : Rel') (n : ℕ): RelType'
    | complex
      (t1 : RelType' ) (m1 m2 : Rel'.mult) (t2 : RelType' ) : RelType'
    | intersect (t1 : RelType' ) (t2 : RelType' ) : RelType'
    | add (t1 : RelType' ) (t2 : RelType' ): RelType'
    | sub (t1 : RelType' ) (t2 : RelType' ):
        RelType'
    | append (t1 : RelType' ) (t2 : RelType' ):
        RelType'
    | cartprod (t1 : RelType' ) (t2 : RelType' ):
        RelType'
    | dotjoin (t1 : RelType' ) (t2 : RelType' ) :  RelType'
    | transclos (t : RelType' ):
        RelType'
    | reftransclos (t : RelType' ):
        RelType'
    | transpose (t : RelType' ):
        RelType'
    | domrestr (t1 : RelType' ) (t2 : RelType' ):
        RelType'
    | rangerestr (t1 : RelType' ) (t2 : RelType' ):
        RelType'

  inductive Rel' : Type :=
    | none : Rel'
    | univ : Rel'
    | iden : Rel'
    | var (name : String) (n : ℕ) (t : RelType') : Rel'
    | add (r1 r2 : Rel') : Rel'
    | cartprod (r1 r2 : Rel') : Rel'
    | dotjoin (r1 r2 : Rel') : Rel'
end

mutual
  def RelType'.hasArity (t : RelType') (n : ℕ) :=
  match t with
    | .sig (m :Rel'.mult) => n = 1
    | .unary_rel r _   => r.hasArity 1 ∧ n = 1
    | .rel r n         => r.hasArity n
    | .constant r n    => r.hasArity n
    | .complex t1 _ _ t2 => ∃ n1 n2, t1.hasArity n1 ∧ t2.hasArity n2 ∧ n1 + n2 = n
    | .intersect t1 t2   => t1.hasArity n ∧ t2.hasArity n
    | .add t1 t2   => t1.hasArity n ∧ t2.hasArity n
    | .sub t1 t2   => t1.hasArity n ∧ t2.hasArity n
    | .append t1 t2   => t1.hasArity n ∧ t2.hasArity n
    | .cartprod t1 t2 => ∃ n1 n2, t1.hasArity n1 ∧ t2.hasArity n2 ∧ n1 + n2 = n
    | .dotjoin t1 t2 => ∃ n1 n2, t1.hasArity n1 ∧ t2.hasArity n2 ∧ n1 + n2 = n + 2
    | .transclos t => t.hasArity 2 ∧ n = 2
    | .reftransclos t => t.hasArity 2 ∧ n = 2
    | .transpose t => t.hasArity 2 ∧ n = 2
    | .domrestr t1 t2 => t1.hasArity 1 ∧ t2.hasArity n
    | .rangerestr t1 t2 => t1.hasArity n ∧ t2.hasArity 1

  def Rel'.hasArity (r : Rel') (n : ℕ) :=
    match r with
    | .none => True
    | .univ => n = 1
    | .iden => n = 2
    | .var _ n t => t.hasArity n
    | .add r1 r2 => r1.hasArity n ∧ r2.hasArity n
    | .cartprod r1 r2 => ∃ n1 n2, r1.hasArity n1 → r2.hasArity n2 → n1 + n2 = n
    | .dotjoin r1 r2 => ∃ n1 n2, r1.hasArity n1 → r2.hasArity n2 → n1 + n2 = n + 2
end

def RelType (n : ℕ):= { r : RelType'  // r.hasArity n }

namespace Rel'
  inductive equal : Rel' → Rel' → Prop :=
  | refl (r : Rel') : equal r r
  | sym (r1 r2 : Rel') : equal r1 r2 → equal r2 r1
  | trans (r1 r2 r3 : Rel') : equal r1 r2 → equal r2 r3 → equal r1 r3

  inductive subset : Rel' → Rel' → Prop
  | refl (r : Rel') : subset r r
  | trans (r1 r2 r3 : Rel') : subset r1 r2 → subset r2 r3 → subset r1 r3

  axiom subset.antisym {r1 r2 : Rel'} : subset r1 r2 → subset r2 r1 → equal r1 r2

  inductive hasMult : Rel' → mult → Prop
  | set (r : Rel') (m : mult): hasMult r m
  | no : hasMult Rel'.none mult.no
  | some (r : Rel') : ¬ (subset r Rel'.none) → hasMult r mult.some
  | lone (r : Rel') : (∀ r' r'': Rel', ¬ (subset r' Rel'.none) → subset r' r → ¬ (subset r'' Rel'.none) → subset r'' r → equal r' r) → hasMult r mult.one
  | one (r : Rel') : hasMult r mult.lone → hasMult r mult.some → hasMult r mult.one
end Rel'

#check Rel'.subset

inductive hasType' : Rel' → RelType' → Type :=
  -- subset : m univ
  | sig (m : Rel'.mult):
    ∀ (subset : Rel'), subset.subset Rel'.univ → subset.hasMult m
    → hasType' subset (RelType'.sig m)
  -- subset : m superset
  | unary_rel (superset : Rel') (m : Rel'.mult)  (h : superset.hasArity 1):
    ∀ (subset : Rel'), subset.subset superset → subset.hasMult m
    → hasType' subset (RelType'.unary_rel superset m)
  -- -- subrel : subrel
  -- | rel (superrel : R) (n : ℕ) (h: HasArity.hasArity superrel n):
  --   ∀ (subrel : R), subrel ⊂ superrel
  --   → hasType' subrel (RelType.rel R superrel n h)
  -- -- none ∷ constant none, univ ∷ constant univ, id ∷ constant id
  -- | constant (c : R) (n : ℕ) (h : HasArity.hasArity c n):
  --   ∀ (c' : R), c' = c
  --   → hasType' c' (RelType.constant R c n h)
  -- -- r1' ∷ t1 , r2' ∷ t2 → t1 m1 ⟶ m2 t2
  -- -- TODO replace ⋈ by correct operator "⋈*" (left/right)
  -- | complex
  --   (n1 n2 : ℕ)
  --   (t1 : RelType') (m1 m2 : Rel'.mult) (t2 : RelType')
  --    :
  --   ∀ (r1' r2' : R),
  --     hasType' r1' t1 → hasType' r2' t2 →
  --     ∀ (r' : R),
  --       (r' ⊂ r1' ⟶ r2') →
  --     (
  --       (∀ (r1'' : R),
  --         r1'' ⊂ r1' → SetMultPredicates.one r1'' → (mult_to_pred m2 (r1'' ⋈ r')))
  --     ) →
  --     (
  --       (∀ (r1'' : R),
  --         r1'' ⊂ r1' → SetMultPredicates.one r1'' → (hasType' (r1'' ⋈ r') t2))
  --     )
  --       →
  --     (
  --       (∀ (r2'' : R),
  --         r2'' ⊂ r2' → SetMultPredicates.one r2'' → (mult_to_pred m1 (r' ⋈ r2'')))
  --     )
  --       →
  --     (
  --       (∀ (r2'' : R),
  --         r2'' ⊂ r2' → SetMultPredicates.one r2'' → (hasType' (r' ⋈ r2'') t1))
  --     )
  --      →
  --     hasType' r' (RelType'.complex t1 m1 m2 t2)
  -- -- r1' & r2' : t1 & t2
  -- | intersect (n : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' & r2') (RelType'.intersect t1 t2)
  -- -- r1' + r2' : t1 + t2
  -- | add (n : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' + r2') (RelType'.add t1 t2)
  -- -- r1' - r2' : t1 - t2
  -- | sub (n : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R),
  --   hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' - r2') (RelType'.sub t1 t2)
  -- -- r1' ++ r2' : t1 ++ t2
  -- | append (n : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' ++ r2') (RelType'.append t1 t2)
  -- -- TODO cartprod redundant to complex
  -- -- r1' ⟶ r2' : t1 ⟶ t2
  -- | cartprod (n1 n2 : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' ⟶ r2') (RelType'.cartprod t1 t2)
  -- -- r1' ⋈ r2' : t1 ⋈ t2
  -- | dotjoin (n1 n2 : ℕ) (t1 : RelType') (t2 : RelType') :
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' ⋈ r2') (RelType'.dotjoin t1 t2)
  -- -- ^r' : ^t
  -- | transclos (t : RelType'):
  --   ∀ (r' : R), hasType' r' t
  --   → hasType' (^r') (RelType'.transclos t)
  -- -- *r' : *t
  -- | reftransclos (t : RelType'):
  --   ∀ (r' : R), hasType' r' t
  --   → hasType' (^r') (RelType'.reftransclos t)
  -- -- -- ~r' : ~t
  -- -- | transpose (t : RelType R 2):
  -- | transpose (t : RelType'):
  --   ∀ (r' : R), hasType' r' t
  --   → hasType' (~ r') (RelType'.transpose t)
  -- -- r1' <: r2' : t1 <: t2
  -- | domrestr (n : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' <: r2') (RelType'.domrestr t1 t2)
  -- -- -- r1' :> r2' : t1 :> t2
  -- | rangerestr (n : ℕ) (t1 : RelType') (t2 : RelType'):
  --   ∀ (r1' r2' : R), hasType' r1' t1 → hasType' r2' t2
  --   → hasType' (r1' <: r2') (RelType'.rangerestr t1 t2)







-- lemma RelType'.sig.cons { : Type} [TupleSet ] {m : Rel'.mult} :
--   (@RelType'.sig  _ m).arity = some 1 := by dsimp[RelType'.arity]
def RelType.sig ( : Type) [TupleSet ] (m : Rel'.mult) :=
  @Subtype.mk _ (λ r => r.arity = some 1) (@RelType'.sig  _ m) (by dsimp[RelType'.arity])

def RelType.unary_rel ( : Type) [TupleSet ] (m : Rel'.mult) (r : ) (h : HasArity.hasArity r 1):=
  @Subtype.mk _ (λ r => r.arity = some 1) (@RelType'.unary_rel  _ m r h) (by dsimp[RelType'.arity])

def RelType.rel ( : Type) [TupleSet ] (r : ) (n : ℕ) (h : HasArity.hasArity r n):=
  @Subtype.mk _ (λ r => r.arity = some n) (@RelType'.rel  _ r n h) (by dsimp[RelType'.arity])

def RelType.constant ( : Type) [TupleSet ] (c : ) (n : ℕ) (h : HasArity.hasArity c n) :=
  @Subtype.mk _ (λ r => r.arity = some n) (@RelType'.constant  _ c n h) (by dsimp[RelType'.arity])

def RelType.none ( : Type) [TupleSet ] (n : ℕ) :=
  @Subtype.mk _ (λ r => r.arity = some n) (@RelType'.constant  _ ((@SetConstants.none  _)) n arity_none) (by dsimp)

def RelType.univ ( : Type) [TupleSet ] :=
  @Subtype.mk _ (λ r => r.arity = some 1) (@RelType'.constant  _ ((@RelConstants.univ  _)) 1 arity_univ) (by dsimp)

def RelType.iden ( : Type) [TupleSet ] :=
  @Subtype.mk _ (λ r => r.arity = some 2) (@RelType'.constant  _ ((@RelConstants.iden  _)) 2 arity_iden) (by dsimp)

@[simp]
lemma RelType'.arity.cons { : Type} [TupleSet ] {n : ℕ} (t : RelType  n) : t.1.arity = n := by
  cases t with
  | mk val property => dsimp[RelType'.arity]; trivial

def RelType.arity { : Type} [TupleSet ] {n : ℕ} (t : RelType  n) := n
lemma RelType.arity.cons { : Type} [TupleSet ] {n : ℕ} (t : RelType  n) : t.arity = n := by
  cases t with
  | mk val property => dsimp[arity]

def RelType.complex { : Type} [TupleSet ] {n1 : ℕ} (t1 : RelType  n1) (m1 m2 : Rel'.mult) {n2 : ℕ} (t2 : RelType  n2) :=
  @Subtype.mk _ (λ r => r.arity = some (n1 + n2)) (@RelType'.complex  _ t1.1 m1 m2 t2.1) (by simp)

instance ( : Type) [TupleSet ] (n : ℕ) : Intersect (RelType  n) where
  intersect t1 t2 := Subtype.mk (RelType'.intersect t1.1 t2.1) (by simp)

instance ( : Type) [TupleSet ] (n : ℕ) : Add (RelType  n) where
  add t1 t2 := Subtype.mk (RelType'.add t1.1 t2.1) (by simp)

instance ( : Type) [TupleSet ] (n : ℕ) : Sub (RelType  n) where
  sub t1 t2 := Subtype.mk (RelType'.sub t1.1 t2.1) (by simp)

instance ( : Type) [TupleSet ] (n : ℕ) : Append (RelType  n) where
  append t1 t2 := Subtype.mk (RelType'.append t1.1 t2.1) (by simp)

instance ( : Type) [TupleSet ] (n1 n2 : ℕ):
    HCartprod (RelType  n1) (RelType  n2) (outParam (RelType  (n1 + n2))) where
      hCartprod (t1 : RelType  n1) (t2 : RelType  n2) :=
        Subtype.mk (RelType'.cartprod t1.1 t2.1) (by simp)

instance ( : Type) [TupleSet ] (n1 n2 : ℕ):
    HDotjoin (RelType  (n1 + 1)) (RelType  (n2 + 1)) (outParam (RelType  (n1 + n2))) where
      hDotjoin (t1 : RelType  (n1 +1)) (t2 : RelType  (n2 + 1)):=
        Subtype.mk (RelType'.dotjoin t1.1 t2.1) (by simp ; ring_nf ; rw[add_assoc, add_comm] ; simp)

instance ( : Type) [TupleSet ] : Transclos (RelType  2) where
  transclos t := Subtype.mk (RelType'.transclos t.1) (by simp)
instance ( : Type) [TupleSet ] : ReflTransclos (RelType  2) where
  rtransclos t := Subtype.mk (RelType'.transclos t.1) (by simp)
instance ( : Type) [TupleSet ] : Transpose (RelType  2) where
  transpose t := Subtype.mk (RelType'.transpose t.1) (by simp)

instance ( : Type) [TupleSet ] (n : ℕ):
    HDomRestr (RelType  1) (RelType  n) (outParam (RelType  n)) where
      hDomrestr (t1 : RelType  1) (t2 : RelType  n) :=
        Subtype.mk (RelType'.domrestr t1.1 t2.1) (by simp)
instance ( : Type) [TupleSet ] (n : ℕ):
    HRangeRestr (RelType  n) (RelType  1) (outParam (RelType  n)) where
      hRangerestr (t1 : RelType  n) (t2 : RelType  1) :=
        Subtype.mk (RelType'.rangerestr t1.1 t2.1) (by simp)

instance [TupleSet ] {n : ℕ}: Arity (RelType  n) where
  arity             := n
  hasArity _ n'     := n = n'
  arity_consistent  := by simp
