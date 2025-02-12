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
    | unary_rel_to_rel (t : RelType R 1) (r : Rel t):
      subtypeP (RelType.mk.unary_rel Shared.mult.set r) (RelType.mk.rel r)
    | rel_to_unary_rel (t : RelType R 1) (r : Rel t):
      subtypeP (RelType.mk.rel r) (RelType.mk.unary_rel Shared.mult.set r)
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

  -- propositional subtype
  /-- The typeclass behind the notation `a ≺ b` -/
  class PSubtype (α : Type u) where
    /-- `a ≺ b` -/
    isPSubtype : α → α → Prop
  infixl:63 " ≺ "   => PSubtype.isPSubtype

  @[simp]
  instance {R : Type} [TupleSet R] : PSubtype (RelType R arity) where
    isPSubtype  (t1 t2 : RelType R arity) := Subtype.subtypeP t1 t2

namespace Subtype

  variable {R : Type} [TupleSet R]

  theorem subtypeP_subtype {arity : ℕ} (t1 t2 : RelType R arity):
    subtypeP t1 t2 → subtype t1 t2
  := by sorry
end Subtype

section test_subtype
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

  variable (PERSON : ∷ set univ)
  variable (MANN : ∷ set PERSON) -- !!! RelType.unary_rel
  variable (FRAU : ∷ set PERSON)
  variable (MANN' : ∷ set MANN)
  variable (MANN'' : ∷ PERSON) -- !!! RelType.rel
  variable (m : ∷ lone PERSON)

example : MANN.getType ≺ PERSON.getType
  := by aesop
example : MANN.getType ≺ PERSON.getType
  := by aesop
example : MANN'.getType ≺ PERSON.getType
  := by aesop
example : (PERSON - MANN).getType ≺ PERSON.getType
  := by aesop
example : (MANN).getType ≺ (MANN + FRAU).getType
  := by aesop
example : (MANN).getType ≺ (FRAU + MANN).getType
  := by aesop
example (r1 : ∷ some MANN) :
  r1.getType ≺ (MANN + (FRAU - (MANN' & PERSON))).getType
  := by aesop

-- unary_rel set r ≺ rel r
example : MANN.getType ≺ MANN''.getType
  := by aesop
-- rel r ≺ unary_rel set r
example : MANN''.getType ≺ MANN.getType
  := by aesop

variable (C1 : ∷ univ one → some univ)
variable (C2 : ∷ univ set → set univ)
example : C1.getType ≺ C2.getType
:= by aesop

variable (D1 : ∷ MANN one → some FRAU)
variable (D2 : ∷ PERSON some → set PERSON)

/- TODO : aesop is not able to automate the proof for this subtype proposition-/
example : D1.getType ≺ D2.getType
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
  variable {R : Type} [TupleSet R]

  lemma castable {t1 : RelType R arity} (r : Rel t1) (t2 : RelType R arity):
    t1 ≺ t2 → r.relation ∷ t2 :=
  by
    intro h1
    apply subtypeP_subtype at h1
    dsimp [subtype] at h1
    apply h1
    cases r with | mk relation type_pf => apply type_pf

  def cast {t1 : RelType R arity} (r : Rel t1) {t2 : RelType R arity} (subtype_pf : t1 ≺ t2)
  : (Rel t2)
  := Rel.mk
    (r.relation)
    (castable r t2 subtype_pf)

  macro "cast" varName:ident : term
    => do `((Subtype.cast $(varName) (by aesop)))

  macro "cast" varName:ident "∷" typeName:typeExpr: term
    => do `((Subtype.cast $(varName) (by aesop) : ∷ $(typeName)))

  macro "cast" "(" varName:term ")" : term
    => do `((Subtype.cast $(varName) (by aesop)))

  macro "cast" "(" varName:term ")" ":" type:typeExpr : term
    => do `((Subtype.cast $(varName) (by aesop) : ∷ $(type)))

  macro "cast" "(" varName:term ")" "∷" typeName:typeExpr: term
    => do `((Subtype.cast $(varName) (by aesop) : ∷ $(typeName)))
end Subtype

section test_cast
  class  vars  (ThoR_TupleSet  :  Type)  [ThoR.TupleSet  ThoR_TupleSet] where
    PERSON : ∷ set univ
    MANN : ∷ set PERSON
    MANN' : ∷ set MANN
    FRAU : ∷ set PERSON
    m1 : ∷ lone PERSON
    m2 : ∷ lone MANN
    m3 : ∷ lone MANN'

  variable {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]
  namespace preds
/- FIXME : predicate does not depend on vars -> missing typeclass dependency
    see example predicate p1:
    p1 does not depend on any of the above vars. Correspondingly, the dependency on the typeclass vars [vars ThoR_TupleSet] is not part of the typeclass dependencies. However, this dependency has to be present to make the ∻-macro work.
    Otherwise, the application (∻ p1) will bind x with PERSON and there is no variable left to bind, i.e. (∻ p1) <something> will lead to an error.

    Easiest fix seems to be to explicitly add all typeclass dependencies [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet] explicitly to all predicate definitions.
-/
    def p1 {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]
      (x : ∷ set univ) := (x - x) ≡ x
    def p2 {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]
      (x : ∷ set @ vars.PERSON) := x - x ≡ x
    def p3 {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]
      (x : ∷ set @ vars.MANN) := x - x ≡ x
    def p4 {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]
      (x : ∷ set @ vars.MANN') := x - x ≡ x
  end preds

  variable {ThoR_TupleSet : Type} [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]

  #check (∻ preds.p1) vars.PERSON
  #check (∻ preds.p1) (cast vars.MANN : ∷ set univ)
  #check (∻ preds.p1) (cast vars.MANN : _)
  #check (∻ preds.p2) (cast vars.MANN : ∷ set @ vars.PERSON)
  #check (∻ preds.p2) (cast vars.MANN ∷ set @ vars.PERSON)
  #check (∻ preds.p2) (cast vars.MANN : _)
  #check (∻ preds.p2) (cast vars.MANN' : ∷ set @ vars.PERSON)
  #check (∻ preds.p2)
    (cast (cast vars.MANN' ∷ set @ vars.MANN) ∷ set @ vars.PERSON)
  #check (∻ preds.p3) vars.MANN'

/- FIXME : cast macro syntax problem when chaining casts in the following syntax:

    #check (cast (cast vars.MANN' : ∷ set @ vars.MANN) : ∷ set @ vars.MANN)
-/
end test_cast


/- TODO : (by aesop) should be lazily evaluated in coercion
    Otherwise, (by aesop) in the coercion definition does not make sense, as the concrete types t1 and t2 are not known before the coercion has been applied.
-/
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
