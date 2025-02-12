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
  @[aesop unsafe [constructors]]
  inductive subtypeP : {arity : ℕ} → RelType R arity →  RelType R arity → Prop
  where
    | refl (t : RelType R arity) :
      subtypeP t t
    | trans (t1 t2 t3 : RelType R arity) :
      subtypeP t1 t2 → subtypeP t2 t3 → subtypeP t1 t3
    | unary_rel_toSet (t : RelType R 1) (r : Rel t) (m : Shared.mult):
      subtypeP (RelType.mk.unary_rel m r) (RelType.mk.unary_rel Shared.mult.set r)
    | unary_rel (t : RelType R 1) (r : Rel t) (m : Shared.mult):
      subtypeP (RelType.mk.unary_rel m r) r.getType
    | subset (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2):
      r1 ⊂ r2 → subtypeP (r1).getType (r2).getType
    | complex_toSet_l {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 : RelType R arity2) (m1 m2 : Shared.mult) :
      subtypeP (RelType.complex t1 m1 m2 t2) (RelType.complex t1 Shared.mult.set m2 t2)
    | complex_toSome_l {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 : RelType R arity2) (m2 : Shared.mult) :
      subtypeP (RelType.complex t1 Shared.mult.one m2 t2) (RelType.complex t1 Shared.mult.some m2 t2)
    | complex_toLone_l {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 : RelType R arity2) (m2 : Shared.mult) :
      subtypeP (RelType.complex t1 Shared.mult.one m2 t2) (RelType.complex t1 Shared.mult.lone m2 t2)
    | complex_toSet_r {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 : RelType R arity2) (m1 m2 : Shared.mult) :
      subtypeP (RelType.complex t1 m1 m2 t2) (RelType.complex t1 m1 Shared.mult.set t2)
    | complex_toSome_r {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 : RelType R arity2) (m1 : Shared.mult) :
      subtypeP (RelType.complex t1 m1 Shared.mult.one t2) (RelType.complex t1 m1 Shared.mult.some t2)
    | complex_toLone_r {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 : RelType R arity2) (m1 : Shared.mult) :
      subtypeP (RelType.complex t1 m1 Shared.mult.one t2) (RelType.complex t1 m1 Shared.mult.lone t2)
    | complex_subtype_l {arity1 arity2 : ℕ} (t1 t1' : RelType R arity1) (t2 : RelType R arity2) (m1 m2 : Shared.mult) :
      subtypeP t1 t1' →
      subtypeP (RelType.complex t1 m1 m2 t2) (RelType.complex t1' m1 m2 t2)
    | complex_subtype_r {arity1 arity2 : ℕ} (t1 : RelType R arity1) (t2 t2': RelType R arity2) (m1 m2 : Shared.mult) :
      subtypeP t2 t2' →
      subtypeP (RelType.complex t1 m1 m2 t2) (RelType.complex t1 m1 m2 t2')

  @[simp]
  lemma subset_add_r {arity : ℕ} (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2) : r1 ⊂ (r1 + r2) := by sorry

  @[simp]
  lemma subset_add_l {arity : ℕ} (t1 t2 : RelType R arity) (r1 : Rel t1) (r2 : Rel t2) : r1 ⊂ (r2 + r1) := by sorry

  @[simp]
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
:= by aesop

example : (Subtype.subtypeP MANN'.getType PERSON.getType)
:= by aesop

example : (Subtype.subtypeP (PERSON - MANN).getType PERSON.getType)
:= by aesop

example : (Subtype.subtypeP (MANN).getType (MANN + FRAU).getType)
:= by aesop

example : (Subtype.subtypeP (MANN).getType (FRAU + MANN).getType)
:= by aesop

example (r1 : ∷ some MANN) : (Subtype.subtypeP r1.getType (MANN + (FRAU - (MANN' & PERSON))).getType)
:= by aesop

variable (C1 : ∷ univ one → some univ)
variable (C2 : ∷ univ set → set univ)
example : Subtype.subtypeP C1.getType C2.getType
:= by aesop

variable (D1 : ∷ MANN one → some FRAU)
variable (D2 : ∷ PERSON some → set PERSON)

example : Subtype.subtypeP D1.getType D2.getType
:= by
  -- aesop (config := { maxRuleApplications := 200 })
  apply Subtype.subtypeP.trans
  apply Subtype.subtypeP.complex_toSome_l
  apply Subtype.subtypeP.trans
  apply Subtype.subtypeP.complex_toSet_r
  apply Subtype.subtypeP.trans
  apply Subtype.subtypeP.complex_subtype_l
  apply Subtype.subtypeP.unary_rel
  apply Subtype.subtypeP.complex_subtype_r
  apply Subtype.subtypeP.unary_rel

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
    => do `((Subtype.cast $(varName) (by aesop)))

  macro "cast" varName:ident "∷" typeName:typeExpr: term
    => do `((Subtype.cast $(varName) (by aesop) : ∷ $(typeName)))
end Subtype

section test_cast
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

  variable (PERSON : ∷ set univ)
  variable (MANN : ∷ set PERSON)
  variable (FRAU : ∷ set PERSON)
  variable (m : ∷ lone PERSON)

example : (Subtype.subtypeP MANN.getType PERSON.getType)
:= by aesop

  def m_cast :=
    (Subtype.cast
      m
      (by aesop)
      : ∷ set univ
    )


  /-
  ThoR_TupleSet : Type
  inst✝ : TupleSet ThoR_TupleSet
  PERSON : some univ
  m : lone PERSON
  ⊢ some univ
  -/
  def m' := (cast m ∷ set univ)
  def m'' := (cast m : ∷ set univ)
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

  def p (t : ∷ set PERSON) := t - t
  #check (∻ p) (cast m : _)
  #check (∻ p) (cast m : ∷ set PERSON)
  #check (∻ p) (cast m ∷ set PERSON)

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
