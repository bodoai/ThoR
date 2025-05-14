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

  inductive Term
    {R : Type}
    [TupleSet R]
    : List (@Ty R _) →
      (@Ty R _) →
      Type u
      where

    /- ?? expr string ?? fromula string ?? -/
    | rel {n : ℕ} {t : RelType R n} (r : Rel t) : Term ctx (.expression t)

    /- ?? -/
    | var : (ty : @Ty R _) → Member ty ctx → Term ctx ty

    /- expression constants -/
    --| univ
    --| none
    --| iden

    /- binary expression operators -/
    | union
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 + t2))

    | intersect
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 & t2))

    | difference
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 - t2))

    | overwrite
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 ++ t2))

    | domain_restriction
      {n : ℕ}
      {t1 : RelType R 1}
      {t2 : RelType R n}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 <: t2))

    | range_restriction
      {n : ℕ}
      {t1 : RelType R n}
      {t2 : RelType R 1}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 :> t2))

    | dotjoin
      {n m : ℕ}
      {t1 : RelType R (n+1)}
      {t2 : RelType R (m+2)}
      : Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (t1 ⋈ t2))

    /- unary expression operators -/
    | transclos
      {t : RelType R 2}
      : Term ctx (.expression t) →
        Term ctx (.expression (^ t))

    | reflexive_closure
      {t : RelType R 2}
      : Term ctx (.expression t) →
        Term ctx (.expression (* t))

    | transposition
      {t : RelType R 2}
      : Term ctx (.expression t) →
        Term ctx (.expression (~ t))

    /- expression if else -/
    | if_then_else
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term ctx .formula →
        Term ctx (.expression t1) →
        Term ctx (.expression t2) →
        Term ctx (.expression (RelType.ifThenElse t1 t2))

    /- function call from expression ? -/
    --| call -- skip ?

    /- function application / application of argument to call ? -/
    | app
      : Term ctx (.function dom ran) →
        Term ctx dom →
        Term ctx ran

    /- function abstraction -/
    | lam
      : Term (dom :: ctx) ran →
        Term ctx (.function dom ran)

    /- algebra expression number -/
    | number (z : ℤ) : Term ctx .number -- may have to be from N

    /- algebra expression unary operation -/
    | negation : Term ctx .number → Term ctx .number

    /- algebra expression binary operation -/
    | add
      : Term ctx .number →
      Term ctx .number →
      Term ctx .number

    | sub
      : Term ctx .number →
      Term ctx .number →
      Term ctx .number

    | mul
      : Term ctx .number →
        Term ctx .number →
        Term ctx .number

    | div
      : Term ctx .number →
        Term ctx .number →
        Term ctx .number

    | rem
      : Term ctx .number →
        Term ctx .number →
        Term ctx .number

    /- algebra expression card operation (rel operation)-/
    | card
      {n : ℕ}
      {t : RelType R n}
      : Term ctx (.expression t) →
        Term ctx .number

    /- formula unary rel bool operator-/
    | no
      {n : ℕ}
      {t : RelType R n}
      : Term ctx (.expression t) →
        Term ctx .formula

    | one
      {n : ℕ}
      {t : RelType R n}
      : Term ctx (.expression t) →
        Term ctx .formula

    | lone
      {n : ℕ}
      {t : RelType R n}
      : Term ctx (.expression t) →
        Term ctx .formula

    | some
      {n : ℕ}
      {t : RelType R n}
      : Term ctx (.expression t) →
        Term ctx .formula

    /- formula unary logic operator -/
    | not : Term ctx .formula → Term ctx .formula

    /- formula binary logic operator -/
    | or
      : Term ctx .formula →
        Term ctx .formula →
        Term ctx .formula

    | and
      : Term ctx .formula →
        Term ctx .formula →
        Term ctx .formula

    | implication
      : Term ctx .formula →
        Term ctx .formula →
        Term ctx .formula

    | equivalent
      : Term ctx .formula →
        Term ctx .formula →
        Term ctx .formula

    /- formula if else-/
    | f_if_then_else
      : Term ctx .formula →
        Term ctx .formula →
        Term ctx .formula →
        Term ctx .formula

    /- formula algebraic comparison operator -/
    | algebraic_leq
      : Term ctx .number →
        Term ctx .number →
        Term ctx .formula

    | algebraic_geq
      : Term ctx .number →
        Term ctx .number →
        Term ctx .formula

    | algebraic_eq
      : Term ctx .number →
        Term ctx .number →
        Term ctx .formula

    | algebraic_lt
      : Term ctx .number →
        Term ctx .number →
        Term ctx .formula

    | algebraic_gt
      : Term ctx .number →
        Term ctx .number →
        Term ctx .formula

    /- formula relation comparison operation -/
    | in
      {n : ℕ}
      {t1 t2 : RelType R n}
      (ctx : List (@Ty R _) := [])
      : (expression1 : Term ctx (.expression t1)) →
        (expression2 : Term ctx (.expression t2)) →
        Term ctx .formula

    | eq
      {n : ℕ}
      {t1 t2 : RelType R n}
      (ctx : List (@Ty R _) := [])
      : (expression1 : Term ctx (.expression t1)) →
        (expression2 : Term ctx (.expression t2)) →
        Term ctx .formula

    | neq
      {n : ℕ}
      {t1 t2 : RelType R n}
      (ctx : List (@Ty R _) := [])
      : (expression1 : Term ctx (.expression t1)) →
        (expression2 : Term ctx (.expression t2)) →
        Term ctx .formula

    /- formula quantification -/
    -- | q_all {n : ℕ} {t : RelType R n} : Term ctx (.function (.expression t) ran) → Term ctx .formula -- (f : (Rel t) → Formula): Formula

    /- formula let declaration ? -/
    -- | let

    /- type expression ??-/


  def Term.eval
    {R : Type}
    [TupleSet R]
    {ctx: List (@Ty R _)}
    {ty : @Ty R _}
    (t : @Term R _ ctx ty)
    (env : HList Ty.eval ctx)
    : ty.eval :=
      match t with
      | .rel r => r

      | .var t h => env.get h

      /- binary expression operators -/
      | .intersect r1 r2 => (r1.eval env) & (r2.eval env)
      | .union r1 r2 => HAdd.hAdd (r1.eval env) (r2.eval env)
      | .difference r1 r2 => (r1.eval env) - (r2.eval env)
      | .overwrite r1 r2 => (r1.eval env) ++ (r2.eval env)
      | .domain_restriction r1 r2 => (r1.eval env) <: (r2.eval env)
      | .range_restriction r1 r2 => (r1.eval env) :> (r2.eval env)
      | .dotjoin r1 r2 => (r1.eval env) ⋈ (r2.eval env)

      /- unary expression operators -/
      | .transclos r => ^ (r.eval env)
      | .reflexive_closure  r => * (r.eval env)
      | .transposition r => ~ (r.eval env)

      /- expression if else -/
      | .if_then_else f r1 r2 => HIfThenElse.hIfThenElse (f.eval env) (r1.eval env) (r2.eval env)

      | .lam b => λ x => b.eval (x :: env)
      | .app f a => f.eval env (a.eval env)

      | .number z => z

      /- algebra expression unary operation -/
      | .negation z => - (z.eval env)

      /- algebra expression binary operation -/
      | .add z1 z2 => (z1.eval env) + (z2.eval env)
      | .sub z1 z2 => (z1.eval env) - (z2.eval env)
      | .div z1 z2 => (z1.eval env) / (z2.eval env)
      | .mul z1 z2 => (z1.eval env) * (z2.eval env)
      | .rem z1 z2 => (z1.eval env) % (z2.eval env)

      /- algebra expression card operation (rel operation)-/
      | .card r => Card.card (r.eval env)

      /- formula unary rel bool operator-/
      | .no r => SetMultPredicates.no (r.eval env)
      | .one r => SetMultPredicates.one (r.eval env)
      | .lone r => SetMultPredicates.lone (r.eval env)
      | .some r => SetMultPredicates.some (r.eval env)

      /- formula unary logic operator -/
      | .not f => ¬ (f.eval env)

      /- formula binary logic operator -/
      | .or f1 f2 => (f1.eval env) ∨ (f2.eval env)
      | .and f1 f2 => (f1.eval env) ∧ (f2.eval env)
      | .implication f1 f2 => (f1.eval env) → (f2.eval env)
      | .equivalent f1 f2 => (f1.eval env) = (f2.eval env)

      /- formula if else -/
      | .f_if_then_else f1 f2 f3 =>
        ((f1.eval env) -> (f2.eval env)) ∧ (¬ (f1.eval env) → (f2.eval env))

      /- formula algebraic comparison operator -/
      | .algebraic_leq z1 z2 => (z1.eval env) <= (z2.eval env)
      | .algebraic_geq z1 z2 => (z1.eval env) >= (z2.eval env)
      | .algebraic_lt z1 z2 => (z1.eval env) < (z2.eval env)
      | .algebraic_gt z1 z2 => (z1.eval env) > (z2.eval env)
      | .algebraic_eq z1 z2 => (z1.eval env) = (z2.eval env)

      /- formula relation comparison operation -/
      | .in _ r1 r2 => (r1.eval env) ⊂ (r2.eval env)
      | .eq _ r1 r2 => (r1.eval env) ≡ (r2.eval env)
      | .neq _ r1 r2 => (r1.eval env) ≢  (r2.eval env)

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
    Term.in (ctx := _)
      (expression1 := Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
      (expression2 := Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
  )

-- pred_in2 [x : set univ] {
--    x in univ
-- }
def pred_in2 :=
  @Term.lam _ _ _ [] _ (
    Term.in (ctx := _)
      (expression1 := Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
      (expression2 := Term.rel (@vars.UNIV ThoR_TupleSet _ _))
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
      Term.in (ctx := _)
        (expression1 := Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
        (expression2 := Term.rel (@vars.UNIV ThoR_TupleSet _ _))
    )
  )

-- pred_in3[univ,univ]
example : (Term.app (Term.app (@pred_in3 ThoR_TupleSet _ _) (Term.rel (@vars.UNIV ThoR_TupleSet _ _))) (Term.rel (@vars.UNIV ThoR_TupleSet _ _))).eval [] := by
  simp [Term.eval]
  simp [HList.get]
  apply Set.subset_refl

-- fun1 [x : set univ, y : set univ] : univ {
--    x & y
-- }
def fun1 :=
  @Term.lam ThoR_TupleSet _ (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) [] _ (
    @Term.lam ThoR_TupleSet _ (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) _ _ (
      Term.intersect
        (Term.var (Ty.expression (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) (Member.head))
        (Term.rel (@vars.UNIV ThoR_TupleSet _ _))
    )
  )
