/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.quant
import ThoR.Relation.Quantification
import ThoR.Relation.Rel
-- import ThoR.Relation.Elab

import ThoR.Semantics.RelList

namespace ThoR.Semantics

variable (R : Type) [TupleSet R]

--   | cons : β i → HList β is → HList β (i::is)

  inductive HFunc {γ : Type w} {α : Type v} (β : α → Type u): List α → Type (max u v w) where
    | const : γ → HFunc β []
    | abstraction : (β i → HFunc β is) → HFunc β (i::is)
    | application : HFunc β (i::is) → β i → HFunc β is

--  abbrev RelIndex (R : Type) [TupleSet R] := λ (type : RelTypeWithArity R) => Rel type.2

  -- abbrev RelFunc (R : Type) [TupleSet R] {γ : Type w}:= @HFunc _ (λ (type : RelTypeWithArity R) => Rel type.2) γ


  inductive SemType {R : Type} [TupleSet R] : Type u where
    | number -- ℤ
    | formula -- Prop
    | expression : {n : ℕ} → (rel_type : RelType R n) → SemType -- Rel rel_type
    | expression_list : (indices : List (RelTypeWithArity R)) → SemType -- RelList indices
    | function : SemType → SemType → SemType -- st1.eval → st2.eval

  inductive Term {R : Type} [TupleSet R] : @SemType R _ → Type u where
    | rel {n : ℕ} {t : RelType R n} (r : Rel t) : Term (.expression t)

    | intersect {n : ℕ} {t1 t2 : RelType R n} : Term (.expression t1) → Term (.expression t2)  → Term (.expression (t1 & t2))
    | transclos {t : RelType R 2} : Term (.expression t) → Term (.expression (^ t))

    | if_then_else {n : ℕ} {t1 t2 : RelType R n} : Term .formula → Term (.expression t1) → Term (.expression t2) → Term (.expression (RelType.ifThenElse t1 t2))

    | pred {n : ℕ} {t : RelType R n} : (Rel t → Term .formula) → Term (.function (.expression_list indices) .formula)

    | pred_application {indices : List (RelTypeWithArity R)} : Term (.function (.expression_list indices) .formula) → RelList R indices → Term .formula

    | number (z : ℤ) : Term .number
    | negation : Term .number → Term .number
    | add : Term .number → Term .number → Term .number
    | card {n : ℕ} {t : RelType R n} : Term (.expression t) → Term .number

    | lone {n : ℕ} {t : RelType R n} : Term (.expression t) → Term .formula

    | not : Term .formula → Term .formula
    | or : Term .formula → Term .formula → Term .formula

    | f_if_then_else : Term .formula → Term .formula → Term .formula → Term .formula

    | a_lt : Term .number → Term .number → Term .formula

    | in {n : ℕ} {t1 t2 : RelType R n} : Term (.expression t1) → Term (.expression t2) → Term .formula

    | q_all {n : ℕ} {t : RelType R n} : Term (.function (.expression t) ran) → Term .formula -- (f : (Rel t) → Formula): Formula

end ThoR.Semantics

open ThoR.Semantics
open ThoR
class vars (R : Type) [TupleSet R] where
  UNIV : Rel (RelType.mk.sig R Shared.mult.set)
  Time : Rel (RelType.mk.sig R Shared.mult.set)

variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]

-- @[default_instance]
-- instance : ThoR.TupleSet ThoR_TupleSet := by sorry

-- @[default_instance]
-- instance : vars ThoR_TupleSet := by sorry


def u := Term.rel (@vars.UNIV ThoR_TupleSet _ _)
#check u

#check Term.in (@u ThoR_TupleSet _ _) (@u ThoR_TupleSet _ _)


#check @HFunc.const  _ _ (RelType ThoR_TupleSet) (Term.in (@u ThoR_TupleSet _ _) (@u ThoR_TupleSet _ _))

#check HFunc.abstraction (
    λ (r3 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
      HFunc.const (
        (Term.in (Term.rel r3) (Term.rel r3))
      )
  )

#check
  HFunc.abstraction (
    λ (r2 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
      HFunc.abstraction (
        λ (r3 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
          HFunc.const (
            (Term.in (Term.rel r2) (Term.rel r3))
          )
      )
  )

#check
  HFunc.abstraction (
    λ (r1 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
      HFunc.abstraction (
        λ (r2 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
          HFunc.abstraction (
            λ (r3 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
              HFunc.const (
                Term.or (Term.in (Term.rel r1) (Term.rel r2)) (Term.in (Term.rel r2) (Term.rel r3))
              )
          )
      )
  )

def pred3 :=
  HFunc.abstraction (
    λ (r1 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
      HFunc.abstraction (
        λ (r2 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
          HFunc.abstraction (
            λ (r3 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
              HFunc.const (
                Term.or (Term.in (Term.rel r1) (Term.rel r2)) (Term.in (Term.rel r2) (Term.rel r3))
              )
          )
      )
  )

  -- inductive HFunc {α : Type v} (β : α → Type u) (γ : Type w): List α → Type (max u v w) where
  --   | const : γ → HFunc β γ []
  --   | abstraction : (β i → HFunc β γ is) → HFunc β γ (i::is)
  --   | application : β i → HFunc β γ (i::is) → HFunc β γ is

#check pred3 _
#check
  HFunc.application (
    HFunc.application (
      HFunc.application (pred3 ThoR_TupleSet) (@vars.UNIV ThoR_TupleSet _ _)
    ) (@vars.UNIV ThoR_TupleSet _ _)
  ) (@vars.UNIV ThoR_TupleSet _ _)
