/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Rel

-- subtype relation: ⊏

#check Subtype

namespace ThoR

  /-- The typeclass behind the notation `a ⊏ b` -/
  class Subtype (α : Type u) where
    /-- `a ⊂ b` -/
    subtype : α → α → Prop
  infixl:63 " ⊏ "   => Subtype.subtype

  -- TODO This is a dummy implementation of Subtype for Typed such
  --      that all TypedRels of same arity are subtypes to each other.
  instance {R : Type} [TupleSet R] : ThoR.Subtype (RelType R arity) where
    subtype  (t1 t2 : RelType R arity) := True

  namespace Rel
    lemma isOfSupertype {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}
      (r : Rel t1): t1 ⊏ t2 → r.relation ∷ t2 := by
        sorry
  def toSupertype {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}
      (r : Rel t1) (h : t1 ⊏ t2) : Rel t2:=
        Rel.mk r.relation (r.isOfSupertype h)
  end Rel

  -- instance (R : Type) [TupleSet R] (arity : ℕ) (type : RelType R arity) (r : (Rel type)):
  --   CoeDep (Rel type) r (RelType R arity) where
  --   coe := r.getType

  lemma isSubtype {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity) : t1 ⊏ t2 := by sorry

  def mkSupertype {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity)
    (r : (Rel t1)) : (Rel t2) := r.toSupertype (isSubtype t1 t2)

  instance {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity) (r : (Rel t1)):
    CoeDep (Rel t1) r (Rel t2) where
    coe := mkSupertype t1 t2 r

end ThoR
