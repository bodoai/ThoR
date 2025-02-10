/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR


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
  inductive subtypeP : RelType R arity →  RelType R arity → Prop
  where
    | refl (t : RelType R arity) : subtypeP t t
    | trans (t1 t2 t3 : RelType R arity) : subtypeP t1 t2 → subtypeP t2 t3 → subtypeP t1 t3

  @[simp]
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
  variable {R : Type} [TupleSet R]
  def subtypeC_same_arity  {arity : ℕ} (t1 t2 : RelType R arity)
  := true

  def RelType_arity_cast (arity1 arity2 : ℕ) (t : RelType R arity1) (p : arity1 = arity2): (RelType R arity2) := p ▸ t

  def subtypeC (t1 : RelType R arity1) {arity2 : ℕ} (t2 : RelType R arity2)
  :=
    if (p : arity1 = arity2)
    then false
    else true -- subtypeC_same_arity t1 t2

  @[simp]
  theorem subtypeC_subtypeP (t1 t2 : RelType R arity):
      subtypeC t1 t2 → subtypeP t1 t2
  := by sorry

  theorem subtypeC_subtype (t1 t2 : RelType R arity):
      subtypeC t1 t2 → subtype t1 t2
  := by aesop

  @[simp]
  lemma castable' (r : R) (t1 t2 : RelType R arity):
    r ∷ t1 → subtypeC t1 t2 → r ∷ t2 :=
  by
    intro h1 h2
    apply subtypeC_subtype at h2
    aesop

  lemma castable {t1 : RelType R arity} (r : Rel t1) (t2 : RelType R arity):
    subtypeC t1 t2 → r.relation ∷ t2 :=
  by
    apply castable'
    cases r with
    | mk relation type_pf => aesop

  def cast {t1 : RelType R arity} (r : Rel t1) {t2 : RelType R arity} (subtype_pf : subtypeC t1 t2)
  : (Rel t2)
  := Rel.mk
    (r.relation)
    (castable r t2 subtype_pf)
end Subtype

section test_cast
  variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet]

  variable (PERSON : ∷ some univ)
  variable (m : ∷ lone PERSON)

  #check ∷ some univ

  #check (∷ lone univ)
  def m_cast :
    (∷ some univ) -- target type for cast
  :=
    Subtype.cast
      m -- to be cast relation
      (by dsimp[Subtype.subtypeC]) -- castability proof

  #check m
  #check m_cast

  variable (n : ∷ univ lone → some univ)
  def n_cast :
    (∷ univ set → set univ) -- target type for cast
  :=
    Subtype.cast
      n -- to be cast relation
      (by dsimp[Subtype.subtypeC]) -- castability proof
  #check n
  #check n_cast

/- TODO: Rel.Elab-Macro that works similar to '∷ typeExpr`, but does create the corresponding RelType and not the corresponding Type value. -/

/- TODO inheritance tree → type hierarchy that can be read by cast function (macro) -/
end test_cast
