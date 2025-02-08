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

  namespace SetbasedSubtype
    variable {R : Type} [TupleSet R] {arity : ℕ}
    def isSubtype (t1 t2 : RelType R arity) := ∀ (r : R), r ∷ t1 → r ∷ t2
    lemma refl : Reflexive (@isSubtype R _ arity) := by simp [SetbasedSubtype.isSubtype, Reflexive]
    lemma trans : Transitive (@isSubtype R _ arity) := by
      dsimp [Transitive]
      intro t1 t2 t3 h1 h2 r h0
      aesop
  end SetbasedSubtype

  /-- The typeclass behind the notation `a ⊏ b` -/
  class Subtype (α : Type u) where
    /-- `a ⊏ b` -/
    isSubtype : α → α → Prop
    refl : Reflexive isSubtype -- ∀ (t : α), isSubtype t t
    trans : Transitive isSubtype --∀ (t1 t2 t3 : α), isSubtype t1 t2 → isSubtype t2 t3 → isSubtype t1 t3
  infixl:63 " ⊏ "   => Subtype.isSubtype

  instance {R : Type} [TupleSet R] : Subtype (RelType R arity) where
    isSubtype  (t1 t2 : RelType R arity) := SetbasedSubtype.isSubtype t1 t2
    refl := SetbasedSubtype.refl
    trans := SetbasedSubtype.trans

  @[simp]
  lemma unfoldSubtype {R : Type} [TupleSet R] (t1 t2 : RelType R arity) :
    t1 ⊏ t2 ↔ SetbasedSubtype.isSubtype t1 t2 := by aesop

  -- propositional subtype
  /-- The typeclass behind the notation `a ≺ b` -/
  class PSubtype (α : Type u) where
    /-- `a ≺ b` -/
    isPSubtype : α → α → Prop
  infixl:63 " ≺ "   => PSubtype.isPSubtype

  namespace PropositionalSubtype
    @[aesop safe [constructors, cases]]
    inductive isPSubtype {R : Type} [TupleSet R] : {arity : ℕ} → RelType R arity →  RelType R arity → Prop where
    | refl (t : RelType R arity) : isPSubtype t t
    | trans (t1 t2 t3 : RelType R arity) : isPSubtype t1 t2 → isPSubtype t2 t3 → isPSubtype t1 t3
  end PropositionalSubtype

  @[simp]
  instance {R : Type} [TupleSet R] : PSubtype (RelType R arity) where
    isPSubtype  (t1 t2 : RelType R arity) := PropositionalSubtype.isPSubtype t1 t2

  @[simp]
  lemma isPsubtype_refl {R : Type} [TupleSet R] {arity : ℕ} (t : RelType R arity) : t ≺ t := by constructor

  theorem PSubtype_implies_SetbasedSubtype {R : Type} [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
    PropositionalSubtype.isPSubtype t1 t2 → SetbasedSubtype.isSubtype t1 t2 := by
    intro h
    induction h with
    | refl t => apply SetbasedSubtype.refl
    | trans t1 t2 t3 _ _ ih1 ih2 =>
      apply Subtype.trans ih1 ih2

  @[simp]
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
  class CSubtype (α β : Type u) where
    /-- `a ≺≺ b` -/
    isCSubtype : α → β → Bool
  infixl:63 " ≺≺ "   => CSubtype.isCSubtype
  @[simp]

  instance {R : Type} [TupleSet R] : CSubtype (RelType R arity1) (RelType R arity2) where
    isCSubtype  (t1 : RelType R arity1) (t2 : RelType R arity2)  := ComputationalSubtype.isCSubtype t1 t2

  theorem CSubtype_implies_PSubtype {R : Type} [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
      t1 ≺≺ t2 → t1 ≺ t2 := by sorry

  theorem CSubtype_implies_Subtype {R : Type} [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
      t1 ≺≺ t2 → t1 ⊏ t2 := by
      intro h
      apply PSubtype_implies_Subtype
      apply CSubtype_implies_PSubtype
      apply h


  namespace Rel
    @[simp]
    lemma isOfSupertype {R : Type} [TupleSet R] {arity : ℕ} (r : R) (t1 t2 : RelType R arity): r ∷ t1 → t1 ⊏ t2 → r ∷ t2 :=
    by aesop

    lemma isOfSupertype' {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}
      (r : Rel t1): t1 ⊏ t2 → r.relation ∷ t2 :=
    by
      dsimp [Subtype.isSubtype]
      intro h
      cases r with
      | mk relation proof =>
        dsimp
        apply h
        apply proof

    def toSupertype {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity} (r : Rel t1) (h : t1 ⊏ t2) : Rel t2:=
          Rel.mk r.relation (r.isOfSupertype' h)

    def cast {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity} (r : Rel t1) (h : t1 ≺ t2) : Rel t2:=
          Rel.mk r.relation (r.isOfSupertype' (PSubtype_implies_Subtype _ _ _ h))
  end Rel

  open PropositionalSubtype
  section test_cast
    variable {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 t3 : RelType R arity} (r : Rel t1)
    variable (h1 : t1 ≺ t2) (h2 : t2 ≺ t3)

    set_option trace.aesop true in
    -- set_option trace.aesop.tree true in
    lemma l1 : PropositionalSubtype.isPSubtype t1 t3 := by aesop
      -- apply PropositionalSubtype.isPSubtype.trans
      -- <;> aesop?

    lemma l2 : t1 ≺ t3 := by aesop

    set_option trace.aesop true in
    lemma l3 : t1 ⊏ t3 := by aesop

--    set_option trace.aesop true in
    def r2 : Rel t1 := r.cast (by aesop)

    def r3 : Rel t3 := r.cast (by aesop)
  end test_cast

  -- instance (R : Type) [TupleSet R] (arity : ℕ) (type : RelType R arity) (r : (Rel type)):
  --   CoeDep (Rel type) r (RelType R arity) where
  --   coe := r.getType

  -- @[simp]
  -- lemma isSubtype {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity) : t1 ≺ t2 → t1 ⊏ t2 := by sorry

  set_option trace.aesop true in
  def mkSupertype {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity)
    (r : (Rel t1)) : (Rel t2) := r.toSupertype (by aesop)

  instance {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity) (r : (Rel t1)):
    CoeDep (Rel t1) r (Rel t2) where
--    coe := mkSupertype t1 t2 r
    coe := Rel.mk r.relation (Rel.isOfSupertype r.relation t1 t2 r.type_pf (by aesop))

end ThoR
