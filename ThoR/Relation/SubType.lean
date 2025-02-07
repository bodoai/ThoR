/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Rel

-- subtype relation: ⊏

#check Subtype

namespace ThoR
#print Reflexive

  /-- The typeclass behind the notation `a ⊏ b` -/
  class Subtype (α : Type u) where
    /-- `a ⊏ b` -/
    isSubtype : α → α → Prop
    refl : Reflexive isSubtype -- ∀ (t : α), isSubtype t t
    trans : Transitive isSubtype --∀ (t1 t2 t3 : α), isSubtype t1 t2 → isSubtype t2 t3 → isSubtype t1 t3
  infixl:63 " ⊏ "   => Subtype.isSubtype

  -- TODO This is a dummy implementation of Subtype for RelType such
  --      that all RelTypes of same arity are subtypes to each other.
  @[simp]
  instance {R : Type} [TupleSet R] : Subtype (RelType R arity) where
    isSubtype  (t1 t2 : RelType R arity) := ∀ (r : R), r ∷ t1 → r ∷ t2
    refl := by simp [Reflexive]
    trans := by
      dsimp [Transitive]
      intro t1 t2 t3 h1 h2 r h0
      apply h2
      apply h1
      apply h0

  -- propositional subtype
  /-- The typeclass behind the notation `a ≺ b` -/
  class PSubtype (α : Type u) where
    /-- `a ≺ b` -/
    isPSubtype : α → α → Prop
  infixl:63 " ≺ "   => PSubtype.isPSubtype

  namespace PropositionalSubtype
    inductive isPSubtype {R : Type} [TupleSet R] : {arity : ℕ} → RelType R arity →  RelType R arity → Prop where
    | refl (t : RelType R arity) : isPSubtype t t
    | trans (t1 t2 t3 : RelType R arity) : isPSubtype t1 t2 → isPSubtype t2 t3 → isPSubtype t1 t3
  end PropositionalSubtype

  instance {R : Type} [TupleSet R] : PSubtype (RelType R arity) where
    isPSubtype  (t1 t2 : RelType R arity) := PropositionalSubtype.isPSubtype t1 t2


  theorem PSubtype_implies_Subtype {R : Type} [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
    t1 ≺ t2 → t1 ⊏ t2 := by
    intro h
    induction h with
    | refl t => apply Subtype.refl
    | trans t1 t2 t3 _ _ ih1 ih2 =>
      apply Subtype.trans ih1 ih2

  namespace ComputationalSubtype
    def isCSubtype {R : Type} [TupleSet R] {arity1 : ℕ} (t1 : RelType R arity1) {arity2 : ℕ} (t2 : RelType R arity2):=
    if (arity1 ≠ arity2) then false else true

/-
ThoR.RelType.unary_rel : {R : Type} → [inst : TupleSet R] → Shared.mult → (r : R) → HasArity.hasArity r 1 → RelType R 1
ThoR.RelType.rel : {R : Type} → [inst : TupleSet R] → {n : ℕ} → (r : R) → HasArity.hasArity r n → RelType R n
ThoR.RelType.constant : {R : Type} → [inst : TupleSet R] → {n : ℕ} → (c : R) → HasArity.hasArity c n → RelType R n
ThoR.RelType.complex : {R : Type} →
  [inst : TupleSet R] → {n1 n2 : ℕ} → RelType R n1 → Shared.mult → Shared.mult → RelType R n2 → RelType R (n1 + n2)
ThoR.RelType.intersect : {R : Type} → [inst : TupleSet R] → {n : ℕ} → RelType R n → RelType R n → RelType R n
ThoR.RelType.add : {R : Type} → [inst : TupleSet R] → {n : ℕ} → RelType R n → RelType R n → RelType R n
ThoR.RelType.sub : {R : Type} → [inst : TupleSet R] → {n : ℕ} → RelType R n → RelType R n → RelType R n
ThoR.RelType.append : {R : Type} → [inst : TupleSet R] → {n : ℕ} → RelType R n → RelType R n → RelType R n
ThoR.RelType.cartprod : {R : Type} →
  [inst : TupleSet R] → {n1 n2 : ℕ} → RelType R n1 → RelType R n2 → RelType R (n1 + n2)
ThoR.RelType.dotjoin : {R : Type} →
  [inst : TupleSet R] → {n1 n2 : ℕ} → RelType R (n1 + 1) → RelType R (n2 + 1) → RelType R (n1 + n2)
ThoR.RelType.transclos : {R : Type} → [inst : TupleSet R] → RelType R 2 → RelType R 2
ThoR.RelType.reftransclos : {R : Type} → [inst : TupleSet R] → RelType R 2 → RelType R 2
ThoR.RelType.transpose : {R : Type} → [inst : TupleSet R] → RelType R 2 → RelType R 2
ThoR.RelType.domrestr : {R : Type} → [inst : TupleSet R] → {n : ℕ} → RelType R 1 → RelType R n → RelType R n
ThoR.RelType.rangerestr : {R : Type} → [inst : TupleSet R] → {n : ℕ} → RelType R n → RelType R 1 → RelType R n */  end ComputationalSubtype
-/

  end ComputationalSubtype

  -- computational subtype
  /-- The typeclass behind the notation `a ≺≺ b` -/
  class CSubtype (α : Type u) where
    /-- `a ≺≺ b` -/
    isCSubtype : α → α → Bool
  infixl:63 " ≺≺ "   => CSubtype.isCSubtype

  instance {R : Type} [TupleSet R] : CSubtype (RelType R arity) where
    isCSubtype  (t1 t2 : RelType R arity) := ComputationalSubtype.isCSubtype t1 t2

  theorem CSubtype_implies_PSubtype {R : Type} [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
      t1 ≺≺ t2 → t1 ≺ t2 := by sorry

  theorem CSubtype_implies_Subtype {R : Type} [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
      t1 ≺≺ t2 → t1 ⊏ t2 := by
      intro h
      apply PSubtype_implies_Subtype
      apply CSubtype_implies_PSubtype
      apply h


  namespace Rel
    lemma isOfSupertype {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}
      (r : Rel t1): t1 ⊏ t2 → r.relation ∷ t2 :=
    by
      dsimp
      intro h
      cases r with
      | mk relation proof =>
        dsimp
        apply h
        apply proof

    def toSupertype {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity} (r : Rel t1) (h : t1 ⊏ t2) : Rel t2:=
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
