/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

-- import ThoR
import ThoR.Relation

namespace ThoR
  namespace Subtype

  variable {R : Type} [TupleSet R] {arity : ℕ}

-- subtype relation
  def subtype (t1 t2 : RelType R arity)
    := ∀ (r : R), r ∷ t1 → r ∷ t2

  namespace subtype
    lemma refl : Reflexive (@subtype R _ arity)
      := by simp [subtype, Reflexive]
    lemma trans : Transitive (@subtype R _ arity)
      := by
        dsimp [Transitive]
        intro t1 t2 t3 h1 h2 r h0
        aesop
  end subtype


end Subtype

namespace Subtype
-- subtype predicate
/- TODO : has to be completed -/
  variable {R : Type} [TupleSet R]
  inductive subtypeP : {arity : ℕ} → RelType R arity →  RelType R arity → Prop
  where
    | refl (t : RelType R arity) :
      subtypeP t t
    | trans (t1 t2 t3 : RelType R arity) :
      subtypeP t1 t2 → subtypeP t2 t3 → subtypeP t1 t3
    | unary_rel (t : RelType R 1) (r : Rel t2) (m : Shared.mult):
      subtypeP (RelType.mk.unary_rel m r) t
    | subset (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2):
      r1 ⊂ r2 → subtypeP (r1).getType (r2).getType

  lemma subset_add_r {arity : ℕ} (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2) : r1 ⊂ (r1 + r2) := by sorry

  lemma subset_add_l {arity : ℕ} (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2) : r1 ⊂ (r2 + r1) := by sorry

  lemma subset_sub {arity : ℕ} (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2) : (r1 -r2) ⊂ r1 := by sorry
end Subtype

namespace Subtype

  variable {R : Type} [TupleSet R]

  theorem subtypeP_subtype {arity : ℕ} (t1 t2 : RelType R arity):
    subtypeP t1 t2 → subtype t1 t2
  := by sorry
end Subtype

section test_subtype
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

  variable (PERSON : ∷ set univ)
  variable (MANN : ∷ set PERSON)
  variable (FRAU : ∷ set PERSON)
  variable (MANN' : ∷ set MANN)
  variable (m : ∷ lone PERSON)

example : (Subtype.subtypeP MANN.getType PERSON.getType)
:= by
    apply Subtype.subtypeP.unary_rel

example : (Subtype.subtypeP MANN'.getType PERSON.getType)
:= by
    apply Subtype.subtypeP.trans MANN'.getType MANN.getType PERSON.getType
    apply Subtype.subtypeP.unary_rel
    apply Subtype.subtypeP.unary_rel

example : (Subtype.subtypeP (PERSON - MANN).getType PERSON.getType)
:= by
    apply Subtype.subtypeP.subset
    apply Subtype.subset_sub


example : (Subtype.subtypeP (MANN).getType (MANN + FRAU).getType)
:= by
    apply Subtype.subtypeP.subset
    apply Subtype.subset_add_r

example : (Subtype.subtypeP (MANN).getType (FRAU + MANN).getType)
:= by
    apply Subtype.subtypeP.subset
    apply Subtype.subset_add_l

example (r1 : ∷ some MANN) : (Subtype.subtypeP r1.getType (MANN + (FRAU - (MANN' & PERSON))).getType)
:= by
    apply Subtype.subtypeP.trans r1.getType MANN.getType (MANN + (FRAU - (MANN' & PERSON))).getType
    apply Subtype.subtypeP.unary_rel
    apply Subtype.subtypeP.subset
    apply Subtype.subset_add_r



end test_subtype
  namespace Subtype
-- computational subtype
/- TODO : function subtypeC has to be completed
    - all cases from RelType/hasRelType
    - inheritance tree → type hierarchy -/
  variable {R : Type} [TupleSet R]

  lemma castable {t1 : RelType R arity} (r : Rel t1) (t2 : RelType R arity):
    subtypeP t1 t2 → r.relation ∷ t2 :=
  by
    intro h1
    apply subtypeP_subtype at h1
    dsimp [subtype] at h1
    apply h1
    cases r with | mk relation type_pf => apply type_pf

  def cast {t1 : RelType R arity} (r : Rel t1) {t2 : RelType R arity} (subtype_pf : subtypeP t1 t2)
  : (Rel t2)
  := Rel.mk
    (r.relation)
    (castable r t2 subtype_pf)

  macro "cast" varName:ident : term
    => do `((Subtype.cast $(varName) (by sorry)))

  macro "cast" varName:ident "∷" typeName:typeExpr: term
    => do `((Subtype.cast $(varName) (by sorry) : ∷ $(typeName)))
end Subtype

section test_cast
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

  variable (PERSON : ∷ set univ)
  variable (MANN : ∷ set PERSON)
  variable (FRAU : ∷ set PERSON)
  variable (m : ∷ lone PERSON)

example : (Subtype.subtypeP MANN.getType PERSON.getType)
:= by
    dsimp[Rel.getType]

  def m_cast :=
    (Subtype.cast
      m
      (by sorry)
      : ∷ some univ
    )


  /-
  ThoR_TupleSet : Type
  inst✝ : TupleSet ThoR_TupleSet
  PERSON : some univ
  m : lone PERSON
  ⊢ some univ
  -/
  def m' := (cast m ∷ some univ)
  def m'' := (cast m : ∷ some univ)
  /-
  m' ThoR_TupleSet ?m.6020 : lone ?m.6020 → some univ
  -/
  #check ∻ m'
  #check ∻ m''
  /-
  m' ThoR_TupleSet PERSON m : some univ
  -/
  #check m' ThoR_TupleSet PERSON m

  variable (n : ∷ univ lone → some univ)
  /-
  ThoR_TupleSet : Type
  inst✝ : TupleSet ThoR_TupleSet
  PERSON : some univ
  m : lone PERSON
  n : univ lone → some univ
  ⊢ univ set → set univ
  -/
  def n' := (cast n ∷ univ set → set univ)
  /-
  n' ThoR_TupleSet ?m.6290 : univ set → set univ
  -/
  #check ∻ n'

end test_cast


  instance {R : Type} [TupleSet R] {arity : ℕ} (t1 t2 : RelType R arity) (r : (Rel t1)):
    CoeDep (Rel t1) r (Rel t2) where
--    coe := mkSupertype t1 t2 r
    coe := Rel.mk r.relation (@Subtype.castable R _ arity t1 r t2 (by sorry))

section test_coercion
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]
  variable (PERSON : ∷ some univ)
  #check (PERSON : ∷ PERSON - PERSON)
  def v : ∷ PERSON + PERSON := PERSON
  #check v
end test_coercion
