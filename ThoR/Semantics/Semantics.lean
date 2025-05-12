/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.quant
import ThoR.Relation.Quantification
import ThoR.Relation.Rel
-- import ThoR.Relation.Elab

import ThoR.Semantics.HList

namespace ThoR.Semantics

variable (R : Type) [TupleSet R]

--   | cons : β i → HList β is → HList β (i::is)

  inductive HFunc {return_type : Type w} {α : Type v} (β : α → Type u): List α → Type (max u v w) where
    | const : return_type → HFunc β []
    | abstraction : (β i → HFunc β is) → HFunc β (i::is)
    | application : HFunc β (i::is) → β i → HFunc β is

-- construction follows https://lean-lang.org/documentation/examples/debruijn/
  inductive Ty {R : Type} [TupleSet R] : Type u where
    | number -- ℤ
    | formula -- Prop
    | expression : {n : ℕ} → (rel_type : RelType R n) → Ty -- Rel rel_type
    | function : Ty → Ty → Ty -- type1.eval → type2.eval

  @[reducible]
  def Ty.eval {R : Type} [TupleSet R] (ty : @Ty R _) :=
    match ty with
    | number => ℤ
    | formula => Prop
    | expression rel_type => Rel rel_type
    | function dom ran => dom.eval → ran.eval

  inductive Term {R : Type} [TupleSet R] : List (@Ty R _) → (@Ty R _) → Type u where
    | rel {n : ℕ} {t : RelType R n} (r : Rel t) : Term ctx (.expression t)

    | var : (ty : @Ty R _) → Member ty ctx → Term ctx ty

    | intersect {n : ℕ} {t1 t2 : RelType R n} : Term ctx (.expression t1) → Term ctx (.expression t2)  → Term ctx (.expression (t1 & t2))
    | transclos {t : RelType R 2} : Term ctx (.expression t) → Term ctx (.expression (^ t))

    | if_then_else {n : ℕ} {t1 t2 : RelType R n} : Term ctx .formula → Term ctx (.expression t1) → Term ctx (.expression t2) → Term ctx (.expression (RelType.ifThenElse t1 t2))

    | app   : Term ctx (.function dom ran) → Term ctx dom → Term ctx ran
    | lam   : Term (dom :: ctx) ran → Term ctx (.function dom ran)

    | number (z : ℤ) : Term ctx .number
    | negation : Term ctx .number → Term ctx .number
    | add : Term ctx .number → Term ctx .number → Term ctx .number
    | card {n : ℕ} {t : RelType R n} : Term ctx (.expression t) → Term ctx .number

    | lone {n : ℕ} {t : RelType R n} : Term ctx (.expression t) → Term ctx .formula

    | not : Term ctx .formula → Term ctx .formula
    | or : Term ctx .formula → Term ctx .formula → Term ctx .formula

    | f_if_then_else : Term ctx .formula → Term ctx .formula → Term ctx .formula → Term ctx .formula

    | a_lt : Term ctx .number → Term ctx .number → Term ctx .formula

    | in {n : ℕ} {t1 t2 : RelType R n} : Term ctx (.expression t1) → Term ctx (.expression t2) → Term ctx .formula

    -- | q_all {n : ℕ} {t : RelType R n} : Term ctx (.function (.expression t) ran) → Term ctx .formula -- (f : (Rel t) → Formula): Formula

  def Term.eval {R : Type} [TupleSet R] {ctx: List (@Ty R _)} {ty : @Ty R _} (t : @Term R _ ctx ty) (env : HList Ty.eval ctx): ty.eval :=
    match t with
    | .rel r => r

    | .var t h => env.get h

    | .intersect r1 r2 => (r1.eval env) & (r2.eval env)
    | .transclos r => ^ (r.eval env)
    | .if_then_else f r1 r2 => HIfThenElse.hIfThenElse (f.eval env) (r1.eval env) (r2.eval env)

    | .lam b => λ x => b.eval (x :: env)
    | .app f a => f.eval env (a.eval env)

    | .number z => z
    | .negation z => - (z.eval env)
    | .add z1 z2 => (z1.eval env) + (z2.eval env)
    | .card r => Card.card (r.eval env)

    | .lone r => SetMultPredicates.lone (r.eval env)

    | .not f => ¬ (f.eval env)
    | .or f1 f2 => (f1.eval env) ∨ (f2.eval env)

    | .f_if_then_else f1 f2 f3 =>
      ((f1.eval env) -> (f2.eval env)) ∧ (¬ (f1.eval env) → (f2.eval env))

    | .a_lt z1 z2 => (z1.eval env) < (z2.eval env)

    | .in r1 r2 => (r1.eval env) ⊂ (r2.eval env)

    -- | q_all {n : ℕ} {t : RelType R n} : Term ctx (.function (.expression t) ran) → Term ctx .formula -- (f : (Rel t) → Formula): Formula

end ThoR.Semantics

open ThoR.Semantics
open ThoR
class vars (R : Type) [TupleSet R] where
  UNIV : Rel (RelType.mk.sig R Shared.mult.set)
  Time : Rel (RelType.mk.sig R Shared.mult.set)

variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]

@[default_instance]
instance : ThoR.TupleSet ThoR_TupleSet := by sorry

@[default_instance]
instance : vars ThoR_TupleSet := by sorry

-- pred_in1 [x : set univ] {
--    x in x
-- }
def pred_in1 :=
  @Term.lam ThoR_TupleSet _ _ [] _ (
    Term.in
      (Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
      (Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
  )

-- pred_in2 [x : set univ] {
--    x in univ
-- }
def pred_in2 :=
  @Term.lam _ _ _ [] _ (
    Term.in
      (Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
      (Term.rel (@vars.UNIV ThoR_TupleSet _ _))
  )

-- pred_in1[univ]
example : (Term.app (@pred_in1 ThoR_TupleSet _) (Term.rel (@vars.UNIV ThoR_TupleSet _ _))).eval [] := by
  simp [Term.eval]
  simp [HList.get]
  apply Set.subset_refl

-- pred_in2[univ]
example : (Term.app (@pred_in2 ThoR_TupleSet _ _) (Term.rel (@vars.UNIV ThoR_TupleSet _ _))).eval [] := by
  simp [Term.eval]
  simp [HList.get]
  apply Set.subset_refl

-- pred_in3 [x : set univ, y : set univ] {
--    x in y
-- }
def pred_in3 :=
  @Term.lam ThoR_TupleSet _ (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) [] _ (
    @Term.lam ThoR_TupleSet _ (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) _ _ (
      Term.in
        (Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
        (Term.rel (@vars.UNIV ThoR_TupleSet _ _))
    )
  )

-- pred_in3[univ,univ]
example : (Term.app (Term.app (@pred_in3 ThoR_TupleSet _ _) (Term.rel (@vars.UNIV ThoR_TupleSet _ _))) (Term.rel (@vars.UNIV ThoR_TupleSet _ _))).eval [] := by
  simp [Term.eval]
  simp [HList.get]
  apply Set.subset_refl
