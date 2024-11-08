/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Notation
import ThoR.Relation.HasRelType

-- FIXME: Präzedenzen der Operatoren mit Lean.Notation abgleichen

namespace ThoR

structure Rel {R : Type} [TupleSet R]
  {arity : ℕ} (type : RelType R arity) where
  mk ::
    (relation : R)
    (type_pf : relation ∷ type)

namespace Rel
  def getType {R : Type} [TupleSet R] {arity : ℕ} {type : RelType R arity}
      (_ : (Rel type)) := type
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
        r1.relation ⊂ r2.relation
  instance (R : Type) [TupleSet R] (n : ℕ) (t1 t2 : RelType R n):
    HSubset (Rel t1) (Rel t2) where
      hSubset := subset

  macro "binop_def" name:ident relTypeOp:ident relOp:ident consistencyProof:ident : command
    => do
      `(def $name
          {R : Type} [TupleSet R] {n : ℕ} {t1 t2 : RelType R n}
          (r1 : Rel t1) (r2: Rel t2) :
        Rel ($relTypeOp t1 t2) :=
        Rel.mk
          ($relOp r1.relation r2.relation)
          ($consistencyProof r1.type_pf r2.type_pf)
      )
  macro "binop_inst" name:ident relTypeOp:ident typeClass:ident op:ident : command
    => do
      `(
        instance (R : Type) [TupleSet R] (arity : ℕ) (t1 t2 : RelType R arity):
        $typeClass (Rel t1) (Rel t2) (Rel ($relTypeOp t1 t2)) where
        $op := $name
      )

-- intersect
  binop_def intersect RelType.intersect Intersect.intersect HasRelType.intersect_consistent
  binop_inst intersect RelType.intersect HIntersect hIntersect
-- add
  binop_def add RelType.add Add.add HasRelType.add_consistent
  binop_inst add RelType.add HAdd hAdd
-- sub
  binop_def sub RelType.sub Sub.sub HasRelType.sub_consistent
  binop_inst sub RelType.sub HSub hSub
-- append
  binop_def append RelType.append Append.append HasRelType.append_consistent
  binop_inst append RelType.append HAppend hAppend

/-- cartprod -/
  def cartprod {R : Type} [TupleSet R] {n1 n2 : ℕ}
    {t1 : RelType R n1} {t2 : RelType R n2}
    (r1 : Rel t1) (r2 : Rel t2) :
    Rel (RelType.cartprod t1 t2) :=
    Rel.mk
      (r1.relation ⟶ r2.relation)
      (HasRelType.cartprod_consistent r1.type_pf r2.type_pf)
  instance (R : Type) [TupleSet R] (n1 n2 : ℕ)
    (t1 : RelType R n1) (t2 : RelType R n2):
    HCartprod (Rel t1) (Rel t2) (Rel (RelType.cartprod t1 t2)) where
    hCartprod := Rel.cartprod

/-- dotjoin -/
  def dotjoin {R : Type} [TupleSet R] {n1 n2 : ℕ}
    {t1 : RelType R (n1+1)} {t2 : RelType R (n2+1)}
    (r1 : Rel t1) (r2 : Rel t2) :
    Rel (RelType.dotjoin t1 t2) :=
    Rel.mk
      (r1.relation ⋈ r2.relation)
      (HasRelType.dotjoin_consistent r1.type_pf r2.type_pf)
  instance (R : Type) [TupleSet R] (n1 n2 : ℕ)
    (t1 : RelType R (n1+1)) (t2 : RelType R (n2+1)):
    HDotjoin (Rel t1) (Rel t2) (Rel (RelType.dotjoin t1 t2)) where
    hDotjoin := Rel.dotjoin

  macro "unop_def" name:ident relTypeOp:ident relOp:ident consistencyProof:ident : command
    => do
      `(def $name
          {R : Type} [TupleSet R] {t : RelType R 2} (r: Rel t) :
        Rel ($relTypeOp t) :=
        Rel.mk
          ($relOp r.relation)
          ($consistencyProof r.type_pf)
      )
  macro "unop_inst" name:ident relTypeOp:ident typeClass:ident op:ident : command
    => do
      `(
        instance (R : Type) [TupleSet R] (t : RelType R 2):
          $typeClass (Rel t) (Rel ($relTypeOp t)) where
            $op := $name
      )

-- transclos
  unop_def transclos RelType.transclos Transclos.transclos HasRelType.transclos_consistent
  unop_inst transclos RelType.transclos HTransclos hTransclos
-- reftransclos
  unop_def reftransclos RelType.reftransclos ReflTransclos.rtransclos HasRelType.reftransclos_consistent
  unop_inst reftransclos RelType.reftransclos HReflTransclos hRTransclos
-- reftransclos
  unop_def transpose RelType.transpose Transpose.transpose HasRelType.transpose_consistent
  unop_inst transpose RelType.transpose HTranspose hTranspose

-- domainrestr
  def domrestr {R : Type} [TupleSet R] {n : ℕ} {t1 : RelType R 1} {t2 : RelType R n}
    (r1 : Rel t1) (r2: Rel t2) : Rel (RelType.domrestr t1 t2) :=
        Rel.mk
          (r1.relation <: r2.relation)
          (HasRelType.domrestr_consistent r1.type_pf r2.type_pf)
  instance (R : Type) [TupleSet R] (n : ℕ) (t1 : RelType R 1) (t2 : RelType R n):
    HDomRestr (Rel t1) (Rel t2) (Rel (RelType.domrestr t1 t2)) where
      hDomrestr := Rel.domrestr
-- rangerestr
  def rangerestr {R : Type} [TupleSet R] {n : ℕ} {t1 : RelType R n} {t2 : RelType R 1}
    (r1 : Rel t1) (r2: Rel t2) : Rel (RelType.rangerestr t1 t2) :=
        Rel.mk
          (r1.relation :> r2.relation)
          (HasRelType.rangerestr_consistent r1.type_pf r2.type_pf)
  instance (R : Type) [TupleSet R] (n : ℕ) (t1 : RelType R n) (t2 : RelType R 1):
    HRangeRestr (Rel t1) (Rel t2) (Rel (RelType.rangerestr t1 t2)) where
      hRangerestr := Rel.rangerestr

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
        (HasRelType.hasType.constant
          (@SetConstants.none R _)
          (TupleSet₀.arity_none n)
          (@SetConstants.none R _)
          rfl
        )
    def univ :=
      Rel.mk
        (@RelConstants.univ R _)
        (HasRelType.hasType.constant
          (@RelConstants.univ R _)
          (arity_univ)
          (@RelConstants.univ R _)
          rfl
        )
    def iden :=
      Rel.mk
        (@RelConstants.iden R _)
        (HasRelType.hasType.constant
          (@RelConstants.iden R _)
          (arity_iden)
          (@RelConstants.iden R _)
          rfl
        )
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
    -- (r : Rel unary_rel) → (∷ r)
    def unary_rel {t : RelType R 1} (m : Shared.mult) (r : Rel t) :=
      RelType.unary_rel m r.relation (Rel.arity r)
    -- (r : Rel TupleSet) → (∷ r)
    def rel {n : ℕ} {t : RelType R n} (r : Rel t) :=
      RelType.rel r.relation (Rel.arity r)
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
