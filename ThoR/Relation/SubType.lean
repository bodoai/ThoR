/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

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


-- subtype predicate
/- TODO : has to be completed -/
  inductive subtypeP : RelType R arity →  RelType R arity → Prop
  where
    | refl (t : RelType R arity) : subtypeP t t
    | trans (t1 t2 t3 : RelType R arity) : subtypeP t1 t2 → subtypeP t2 t3 → subtypeP t1 t3

  theorem subtypeP_subtype (t1 t2 : RelType R arity):
    subtypeP t1 t2 → subtype t1 t2
  := by
    intro h
    induction h with
    | refl t => apply subtype.refl
    | trans t1 t2 t3 _ _ ih1 ih2 =>
      apply subtype.trans ih1 ih2
  end Subtype

  namespace Subtype
-- computational subtype
/- TODO : function subtypeC has to be completed
    - all cases from RelType/hasRelType
    - inheritance tree → type hierarchy -/
  variable {R : Type} [TupleSet R]

  def subtypeC_same_arity  {arity : ℕ} (t1 t2 : RelType R arity)
  := match t1 with
    | RelType.sig m h => true
    | RelType.unary_rel m r h1 h2 => true
    | RelType.rel r h => true
    |_ => false

  def RelType_arity_cast (arity1 arity2 : ℕ) (t : RelType R arity1) (p : arity1 = arity2): (RelType R arity2) :=
    p ▸ t

  def subtypeC (t1 : RelType R arity1) {arity2 : ℕ} (t2 : RelType R arity2)
  :=
    if h : arity1 = arity2
    then subtypeC_same_arity
      t1
      (RelType_arity_cast arity2 arity1 t2 (symm h))
    else false

  /- TODO proof -/
  theorem subtypeC_subtypeP (t1 t2 : RelType R arity):
      subtypeC t1 t2 → subtypeP t1 t2
  := by sorry

  theorem subtypeC_subtype (t1 t2 : RelType R arity):
      subtypeC t1 t2 → subtype t1 t2
  := by
    intro h1
    apply subtypeP_subtype
    apply subtypeC_subtypeP
    apply h1

  lemma castable {t1 : RelType R arity} (r : Rel t1) (t2 : RelType R arity):
    subtypeC t1 t2 → r.relation ∷ t2 :=
  by
    intro h1
    apply subtypeC_subtype at h1
    dsimp [subtype] at h1
    apply h1
    cases r with | mk relation type_pf => apply type_pf

  def cast {t1 : RelType R arity} (r : Rel t1) {t2 : RelType R arity} (subtype_pf : subtypeC t1 t2)
  : (Rel t2)
  := Rel.mk
    (r.relation)
    (castable r t2 subtype_pf)

  macro "cast" varName:ident : term
    => do `((Subtype.cast $(varName) (by dsimp[subtypeC,RelType_arity_cast,subtypeC_same_arity])))

  macro "cast" varName:ident "∷" typeName:typeExpr: term
    => do `((Subtype.cast $(varName) (by dsimp[subtypeC,RelType_arity_cast,subtypeC_same_arity]) : ∷ $(typeName)))
end Subtype

section test_cast
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

  variable (PERSON : ∷ set univ)
  variable (MANN : ∷ set PERSON)
  variable (FRAU : ∷ set PERSON)
  variable (m : ∷ lone PERSON)


example : (Subtype.subtypeC (MANN).getType (PERSON).getType) = true
:= by
    dsimp[
      Subtype.subtypeC,
      Subtype.RelType_arity_cast,
      Subtype.subtypeC_same_arity,
      Rel.getType,
      RelType.mk.unary_rel,
      RelType.mk.rel]



#check PERSON.getType
#check m.getType
  lemma l1 : Subtype.subtypeC (MANN).getType (PERSON).getType := by
    dsimp[Rel.getType]
    dsimp[
      Subtype.subtypeC,
      Subtype.RelType_arity_cast,
      Subtype.subtypeC_same_arity,
      Rel.getType,
      RelType.mk.unary_rel,
      RelType.mk.rel]









  def m_cast :=
    (Subtype.cast
      m
      (by
        dsimp[Subtype.subtypeC,Subtype.RelType_arity_cast,Subtype.subtypeC_same_arity])
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
    coe := Rel.mk r.relation (@Subtype.castable R _ arity t1 r t2 (by simp))

section test_coercion
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]
  variable (PERSON : ∷ some univ)
  #check (PERSON : ∷ PERSON - PERSON)
  def v : ∷ PERSON + PERSON := PERSON
  #check v
end test_coercion
