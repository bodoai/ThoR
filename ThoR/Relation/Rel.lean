/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Notation
import ThoR.Relation.HasRelType

-- FIXME: Präzedenzen der Operatoren mit Lean.Notation abgleichen

namespace ThoR

structure Rel {R : Type u} [TupleSet R]
  {arity : ℕ} (type : RelType R arity) where
  mk ::
    (relation : R)
    (type_pf : relation ∷ type)

namespace Rel
  def getType {R : Type} [TupleSet R] {arity : ℕ} {type : RelType R arity}
      (_ : (Rel type)) := type

  lemma getType_type {R : Type} [TupleSet R] {arity : ℕ} {type : RelType R arity} {r : Rel type}: r.getType = type := by dsimp[getType]
  -- instance (R : Type) [TupleSet R] (arity : ℕ) (type : RelType R arity) (r : (Rel type)):
  --   CoeDep (Rel type) r (RelType R arity) where
  --   coe := r.getType

  -- def toRel {R : Type} [TupleSet R] {arity : ℕ} {type : RelType R arity}
  --   (r : Rel type) := r.relation

  -- FIXME Vergleich r ≡ none führt auf Fehler
  def eq {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}
    (r1 : Rel t1) (r2 : Rel t2) := r1.relation = r2.relation
  instance {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}:
    HEqual (Rel t1) (Rel t2) where
      hEqual (r1 : Rel t1) (r2 : Rel t2) := r1.relation = r2.relation
  instance {R : Type} [TupleSet R] {arity : ℕ} {t1 t2 : RelType R arity}:
    HNEqual (Rel t1) (Rel t2) where
      hNEqual (r1 : Rel t1) (r2 : Rel t2) := r1.relation ≠ r2.relation
  -- instance (R : Type) [TupleSet R] (arity : ℕ) (type : RelType R arity) (r : (Rel type)):
  --   CoeDep (Rel type) r R where
  --   coe := r.relation
  theorem arity {R : Type} [TupleSet R] {arity : ℕ} {t : RelType R arity} (r : Rel t):
    HasArity.hasArity r.relation arity := by
      cases r with
      | mk relation type =>
        dsimp
        apply (HasRelType.arity arity relation t)
        apply type
end Rel


namespace Rel
-- subset
  def subset {R : Type} [TupleSet R] {n : ℕ} {t1 t2 : RelType R n}
    (r1 : Rel t1) (r2: Rel t2) : Prop :=
        Subset.subset r1.relation r2.relation
  instance (R : Type) [TupleSet R] (n : ℕ) (t1 t2 : RelType R n):
    HSubset (Rel t1) (Rel t2) where
      hSubset := subset

  local macro "binop_inst"
    typeClass:ident op:ident relTypeOp:ident consistencyProof:ident : command
    => do
      `(
        instance (R : Type) [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
        $typeClass (Rel t1) (Rel t2) (Rel ($relTypeOp t1 t2)) where
        $op r1 r2 := Rel.mk
                ($relTypeOp r1.1 r2.1)
                ($consistencyProof r1.2 r2.2)
      )

-- r1 - r2
  binop_inst HIntersect hIntersect Intersect.intersect HasRelType.intersect_consistent
-- r1 + r2
  binop_inst HAdd hAdd Add.add HasRelType.add_consistent
-- r1 - r2
  binop_inst HSub hSub Sub.sub HasRelType.sub_consistent
-- r1 ++ r2
  binop_inst HAppend hAppend Append.append HasRelType.append_consistent

/-- cartprod -/
  instance (R : Type) [TupleSet R] (n1 n2 : ℕ) (t1 : RelType R n1) (t2 : RelType R n2): HCartprod (Rel t1) (Rel t2) (Rel (t1 ⟶ t2)) where
    hCartprod r1 r2 := Rel.mk
      (r1.1 ⟶ r2.1) (HasRelType.cartprod_consistent r1.2 r2.2)

/-- dotjoin -/
  instance (R : Type) [TupleSet R] (n1 n2 : ℕ)
    (t1 : RelType R (n1+1)) (t2 : RelType R (n2+1)):
    HDotjoin (Rel t1) (Rel t2) (Rel (t1 ⋈ t2)) where
    hDotjoin r1 r2 := Rel.mk
      (Dotjoin.dotjoin r1.1 r2.1) (HasRelType.dotjoin_consistent r1.2 r2.2)

  local macro "unop_inst"
    typeClass:ident op:ident relTypeOp:ident consistencyProof:ident : command
    => do
      `(
        instance (R : Type) [TupleSet R] (t : RelType R 2):
        $typeClass (Rel t) (Rel ($relTypeOp t)) where
        $op r := Rel.mk
                ($relTypeOp r.1)
                ($consistencyProof r.2)
      )

-- ^ r
  unop_inst HTransclos hTransclos Transclos.transclos HasRelType.transclos_consistent
-- * r
  unop_inst HReflTransclos hRTransclos ReflTransclos.rtransclos HasRelType.reftransclos_consistent
-- ~ r
  unop_inst HTranspose hTranspose Transpose.transpose HasRelType.transpose_consistent

-- r1 <: r2
  instance (R : Type) [TupleSet R] (n : ℕ)
    (t1 : RelType R 1) (t2 : RelType R n):
    HDomRestr (Rel t1) (Rel t2) (Rel (t1 <: t2)) where
    hDomrestr r1 r2 := Rel.mk
      (r1.1 <: r2.1) (HasRelType.domrestr_consistent r1.2 r2.2)
-- r1 :> r2
  instance (R : Type) [TupleSet R] (n : ℕ)
    (t1 : RelType R n) (t2 : RelType R 1):
    HRangeRestr (Rel t1) (Rel t2) (Rel (t1 :> t2)) where
    hRangerestr r1 r2 := Rel.mk
      (r1.1 :> r2.1) (HasRelType.rangerestr_consistent r1.2 r2.2)

/-- p => r1 else r2 -/
  instance (R : Type) [TupleSet R] (n : ℕ) (t1 t2 : RelType R n): HIfThenElse (Rel t1) (Rel t2) (Rel (RelType.ifThenElse t1 t2)) where
    hIfThenElse p r1 r2 := Rel.mk
      (IfThenElse.ifThenElse p r1.1 r2.1) (HasRelType.if_then_else_consistent r1.2 r2.2)

-- cardinality
--  def card {R : Type} [TupleSet R] {n : ℕ} {t : RelType R n} (r : Rel t): ℕ := #(r.relation)
  instance (R : Type) [TupleSet R] (n : ℕ) (t : RelType R n):
    Card (Rel t) where
      card r := #(r.relation)
      hasCard r n := #(r.relation) = n
      card_consistent := by simp

-- arity
  -- def arity {R : Type} [TupleSet R] {n : ℕ} {t : RelType R n} (_ : Rel t): ℕ :=
  --   Arity.arity t
  instance (R : Type) [TupleSet R] (n : ℕ) (t : RelType R n):
    Arity (Rel t) where
      arity r := n
      hasArity r n' := n = n'
      arity_consistent := by simp

  instance (R : Type) [TupleSet R] (n : ℕ) (t : RelType R n):
    SetMultPredicates (Rel t) where
      no   r := SetMultPredicates.no   r.relation
      lone r := SetMultPredicates.lone r.relation
      one  r := SetMultPredicates.one  r.relation
      some r := SetMultPredicates.some r.relation
end Rel

namespace Rel
  namespace constant
    variable (R : Type) [TupleSet R]
    variable (n : ℕ)
    def none {n : ℕ} :=
      Rel.mk
        (@SetConstants.none R _)
        (@HasRelType.none.consistent R _ n)
    def univ :=
      Rel.mk
        (@RelConstants.univ R _)
        (HasRelType.univ.consistent R)
    def iden :=
      Rel.mk
        (@RelConstants.iden R _)
        (HasRelType.iden.consistent R)
  end constant
end Rel

namespace RelType
  namespace mk
    variable (R : Type) [TupleSet R]
    -- (r : Rel sig) → (∷ r)
    def sig := @RelType.sig R
  end mk
  namespace mk
    variable {R : Type} [TupleSet R]
    -- (r : Rel unary_rel) → (∷ mult r)
    def unary_rel {t : RelType R 1} (m : Shared.mult) (r : Rel t) :=
      RelType.unary_rel R m r.1 (Rel.arity r)
    -- (r : Rel TupleSet) → (∷ r)
    def rel {n : ℕ} {t : RelType R n} (r : Rel t) :=
      RelType.rel R r.1 n (Rel.arity r)
    -- namespace complex
    --   def both {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2}
    --     (r1 : Rel t1) (m1 m2 : Shared.mult) (r2 : Rel t2) :=
    --     RelType.complex (r1.getType) m1 m2 (r2.getType)
    --   def left {n1 n2 : ℕ} {t1 : RelType R n1}
    --     (r1 : Rel t1) (m1 m2 : Shared.mult) (t2 : RelType R n2) :=
    --     RelType.complex (r1.getType) m1 m2 t2
    --   def right {n1 n2 : ℕ} {t2 : RelType R n2}
    --     (t1 : RelType R n1) (m1 m2 : Shared.mult) (r2 : Rel t2) :=
    --     RelType.complex t1 m1 m2 (r2.getType)
    -- end complex
  end mk
end RelType

/-   Assoziativität des dotjoin:
      1. auf TupleSet zeigen
      2. mit (1) extensionale Gleichheit auf RelType zeigen,
         a) r∷((t1⋈t2)⋈t3) ↔ r∷(t1⋈(t2⋈t3))
         b) Definition ⊑: (∀ (r:R), r∷t1 ↔ r∷t2) → t1 ⊑ t2
      3. Coercion (r1 : t1) :> (r2 : t2) mit
         - r2.relation = r2.relation
         - r2.type = (t2 → t1) r1.type
         für alle t1, t2 mit t1 ⊑ t2
      4. Damit müsste dann für r : ((t1⋈t2)⋈t3) und r' : (t1⋈(t2⋈t3))
         aus r = r' werden:
         r = (Coercion (t1⋈(t2⋈t3)) → ((t1⋈t2)⋈t3)) r'
      5. Axiom proof irrelevance verwenden -> r = r'
-/
end ThoR
