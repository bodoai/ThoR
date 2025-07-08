/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.quant
import ThoR.Relation.Quantification
import ThoR.Relation.Rel
-- import ThoR.Relation.Elab
import ThoR.Relation.ElabCallMacro
namespace ThoR.Semantics

variable (R : Type) [TupleSet R]

inductive TyTy : Type 1 where
  | isTy
  | isPred
    {arity : Nat}
    {R : Type}
    [TupleSet R]
    (rel_type : RelType R arity)
    (quantor_type : Shared.quant)
    (disj : Bool)
    (parameter_count : Nat)
    : TyTy

  | isPred_o
    {arity : Nat}
    {R : Type}
    [TupleSet R]
    (rel_type : RelType R arity)
    (quantor_type : Shared.quant)
    : TyTy

-- construction follows https://lean-lang.org/documentation/examples/debruijn/
  inductive Ty {R : Type} [TupleSet R] : (tt : TyTy) → Type u where
    | number : Ty .isTy-- ℤ
    | formula : Ty .isTy -- Prop
    | expression : {n : ℕ} → (rel_type : RelType R n) → Ty .isTy-- Rel rel_type
    | function : {n : ℕ} → (t : RelType R n) → Ty .isTy → Ty .isTy -- type1.eval → type2.eval
    | pred :
      {arity : ℕ} →
      (rel_type : RelType R arity) →
      (quantor_type : Shared.quant) →
      (disj : Bool) →
      (parameter_count : Nat) →
      Ty (.isPred rel_type quantor_type disj parameter_count)

    | pred_o : (t : RelType R n) → (quantor_type : Shared.quant) → Ty (.isPred_o t quantor_type)
    --| pred_1 : {n : ℕ} → (t : RelType R n) → Ty (.isPred t)
    --| pred_n : {n : ℕ} → (t : RelType R n) → Ty (.isPred t) → Ty (.isPred t)
    | type : (n : ℕ) → Ty .isTy

  inductive Marker : Type u where
    | alloy_predicate
    | alloy_function

  @[reducible]
  def Ty.eval {R : Type} [TupleSet R] {tt : TyTy} (ty : @Ty R _ tt) : Type :=
    match ty with
    | .number => ℤ
    | .formula => Prop
    | .expression rel_type => Rel rel_type
    | .function dom_rel_type ran => Rel dom_rel_type → ran.eval
    | .pred rel_type _ _ n => Vector (Rel rel_type) n → Prop
    | .pred_o t _ => Rel t → Prop
    --| .pred_1 dom_rel_type => Rel dom_rel_type → Prop
    --| .pred_n dom_rel_type p' => Rel dom_rel_type → (p'.eval)
     | Ty.type n => ThoR.RelType R n


-- variable {R : Type} [TupleSet R] (t : RelType R n)
-- #check Ty.pred_1 t

  inductive Term
    {R : Type}
    [TupleSet R]
    : {tt : TyTy} → (ty : @Ty.{u} R _ tt) →
      Type (u+1)
      where

    /- ?? expr string ?? fromula string ?? -/
    | global_rel_var {n : ℕ} {t : RelType R n} (r : Rel t) (name : String): Term (.expression t)
    | local_rel_var {n : ℕ} {t : RelType R n} (r : Rel t): Term (.expression t)

    /- expression constants -/
    --| univ
    --| none
    --| iden

    /- binary expression operators -/
    | union
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 + t2))

    | intersect
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 & t2))

    | difference
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 - t2))

    | overwrite
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 ++ t2))

    | domain_restriction
      {n : ℕ}
      {t1 : RelType R 1}
      {t2 : RelType R n}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 <: t2))

    | range_restriction
      {n : ℕ}
      {t1 : RelType R n}
      {t2 : RelType R 1}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 :> t2))

    | dotjoin
      {n m : ℕ}
      {t1 : RelType R (n+1)}
      {t2 : RelType R (m+2)}
      : Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (t1 ⋈ t2))

    /- unary expression operators -/
    | transclos
      {t : RelType R 2}
      : Term (.expression t) →
        Term (.expression (^ t))

    | reflexive_closure
      {t : RelType R 2}
      : Term (.expression t) →
        Term (.expression (* t))

    | transposition
      {t : RelType R 2}
      : Term (.expression t) →
        Term (.expression (~ t))

    /- expression if else -/
    | if_then_else
      {n : ℕ}
      {t1 t2 : RelType R n}
      : Term .formula →
        Term (.expression t1) →
        Term (.expression t2) →
        Term (.expression (RelType.ifThenElse t1 t2))

    /- function call from expression ? -/
    --| call -- skip ?

    /--bracket definition-/
    | bracket : Term ty → Term ty

    /--predicate definition-/
    | pred_def (name : String) : Term ty → Term ty

    /--function definition-/
    | fun_def (name : String) : Term ty → Term ty
    -- | marker : Marker → Term ty → Term ty
    -- | name : String → Term ty → Term ty

    /- algebra expression number -/
    | number (z : ℤ) : Term .number -- may have to be from N

    /- algebra expression unary operation -/
    | negation : Term .number → Term .number

    /- algebra expression binary operation -/
    | add
      : Term .number →
      Term .number →
      Term .number

    | sub
      : Term .number →
      Term .number →
      Term .number

    | mul
      : Term .number →
        Term .number →
        Term .number

    | div
      : Term .number →
        Term .number →
        Term .number

    | rem
      : Term .number →
        Term .number →
        Term .number

    /- algebra expression card operation (rel operation)-/
    | card
      {n : ℕ}
      {t : RelType R n}
      : Term (.expression t) →
        Term .number

    /- formula unary rel bool operator-/
    | no
      {n : ℕ}
      {t : RelType R n}
      : Term (.expression t) →
        Term .formula

    | one
      {n : ℕ}
      {t : RelType R n}
      : Term (.expression t) →
        Term .formula

    | lone
      {n : ℕ}
      {t : RelType R n}
      : Term (.expression t) →
        Term .formula

    | some
      {n : ℕ}
      {t : RelType R n}
      : Term (.expression t) →
        Term .formula

    /- formula unary logic operator -/
    | not : Term .formula → Term .formula

    /- formula binary logic operator -/
    | or
      : Term .formula →
        Term .formula →
        Term .formula

    | and
      : Term .formula →
        Term .formula →
        Term .formula

    | implication
      : Term .formula →
        Term .formula →
        Term .formula

    | equivalent
      : Term .formula →
        Term .formula →
        Term .formula

    /- formula if else-/
    | f_if_then_else
      : Term .formula →
        Term .formula →
        Term .formula →
        Term .formula

    /- formula algebraic comparison operator -/
    | algebraic_leq
      : Term .number →
        Term .number →
        Term .formula

    | algebraic_geq
      : Term .number →
        Term .number →
        Term .formula

    | algebraic_eq
      : Term .number →
        Term .number →
        Term .formula

    | algebraic_lt
      : Term .number →
        Term .number →
        Term .formula

    | algebraic_gt
      : Term .number →
        Term .number →
        Term .formula

    /- formula relation comparison operation -/
    | in
      {n : ℕ}
      {t1 t2 : RelType R n}
      : (expression1 : Term (.expression t1)) →
        (expression2 : Term (.expression t2)) →
        Term .formula

    | eq
      {n : ℕ}
      {t1 t2 : RelType R n}
      : (expression1 : Term (.expression t1)) →
        (expression2 : Term (.expression t2)) →
        Term .formula

    | neq
      {n : ℕ}
      {t1 t2 : RelType R n}
      : (expression1 : Term (.expression t1)) →
        (expression2 : Term (.expression t2)) →
        Term .formula

    /- function abstraction -/
    | lam (t : RelType R n)
      : (Rel t → Term ran) →
        Term (.function t ran)

    /- function application / application of argument to call ? -/
    | app
      : Term (.function t ran) →
        Term (.expression t) →
        Term ran

    | q_group (quantor_type : Shared.quant) (disj:Bool)
      : Term .formula →
        Term .formula

    | pred
      {arity : Nat}
      {rel_type : RelType R arity}
      {parameter_count : Nat}
      (quantor_type : Shared.quant)
      (disj : Bool)
      :
      (function : (Vector (Rel rel_type) parameter_count) → Term .formula) →
      Term (.pred rel_type quantor_type disj parameter_count)

    /-Test to use PROP instead of Term .formula-/
    /-
    | pred_proped
      {arity : Nat}
      {rel_type : RelType R arity}
      {parameter_count : Nat}
      (quantor_type : Shared.quant)
      (disj : Bool)
      :
      (function : (Vector (Rel rel_type) parameter_count) → Prop) →
      Term (.pred rel_type quantor_type disj parameter_count)
    -/

    /-old pred for comparison-/
    | pred_o {n : ℕ} {t : RelType R n} (quantor_type : Shared.quant)
      : (Rel t → Term .formula) →
        Term (.pred_o t quantor_type)

    | bind
      {arity : Nat}
      {rel_type : RelType R arity}
      {parameter_count : Nat}
      (quantor_type : Shared.quant)
      (disj : Bool)
      : (pred : Term (.pred rel_type quantor_type disj parameter_count) ) →
        Term .formula

    | bind_o {t : RelType R n} (quantor_type : Shared.quant)
      : (pred_o : Term (.pred_o t quantor_type)) →
        Term .formula

    | type {n : ℕ} (t : RelType R n) : Term (.type n)


variable {R : Type} [TupleSet R] (t : RelType R n)

-- try without prop
#check Term.pred (Shared.quant.all) (disj := false)
          (λ (parameter_vector : (Vector (Rel t) 2)) => Term.in
              (expression1 := Term.local_rel_var (parameter_vector.get (Fin.mk 0 (by aesop))))
              (expression2 := Term.local_rel_var (parameter_vector.get 100)) )

#check Fin.ofNat 2 10 -- Fin.ofNat 2 10 : Fin 2
#eval Fin.ofNat 10 2 -- 2
#eval Fin.ofNat 10 10 -- 0

-- try with prop -> what to do to use Term in Prop ?
/-
#check Term.pred_proped (Shared.quant.all) (disj := false)
          (λ (parameter_vector : (Vector (Rel t) 2)) =>
            (Term.in
              (expression1 := Term.local_rel_var (parameter_vector.get (Fin.mk 0 (by aesop))))
              (expression2 := Term.local_rel_var (parameter_vector.get 100))
            )
          )
-/

-- old way, examples
#check Term.pred_o
  (Shared.quant.all)
  (
    λ (q : Rel t) =>
    Term.bind_o
      (Shared.quant.all)
      (Term.pred_o
        (Shared.quant.all)
        (λ (r : Rel t) =>
          Term.in
            (expression1 := Term.local_rel_var q)
            (expression2 := Term.local_rel_var r)
        )
      )
  )

def p1 := Term.pred_o
  (Shared.quant.all)
  (
    λ (q : Rel t) =>
    Term.bind_o
      (Shared.quant.all)
      (Term.pred_o
        (Shared.quant.all)
        (λ (r : Rel t) =>
          Term.in
            (expression1 := Term.local_rel_var q)
            (expression2 := Term.local_rel_var r)
        )
      )
  )


#check (p1 t)

-- set_option diagnostics true
-- set_option diagnostics.threshold 0

example : p1 t = Term.pred_o
  (Shared.quant.all)
  (
    λ (q : Rel t) =>
      Term.bind_o
        (Shared.quant.all)
        (Term.pred_o
          (Shared.quant.all)
          (λ (r : Rel t) =>
              Term.in
                (expression1 := Term.local_rel_var q)
                (expression2 := Term.local_rel_var r)
          )
        )
) := by
  sorry

--set_option diagnostics true
set_option maxHeartbeats 300000

def Vector0 {T : Type} : Vector T 0:= #[].toVector

def curry_pred {T : Type} {parameter_count : Nat} (pred : Vector T (parameter_count + 1) → Prop) :=
  λ (param_list : Vector T parameter_count) => ∀ (x : T), pred (x :: param_list.toList).toVector

def curry_pred_try1 {T : Type} {parameter_count : Nat} (pred : Vector T (parameter_count + 1) → Prop)
  : Vector T parameter_count → Prop :=
    λ (param_list : Vector T parameter_count) =>
    ∀ (x : T), pred (
          (Vector.mk (#[x].append (param_list.toArray))
            (by
              simp
              apply add_comm
            )
          )
        )

def curry_pred_try2 {T : Type} {parameter_count : Nat} (pred : Vector T parameter_count → Prop)
  : Vector T (parameter_count - 1) → Prop :=
  match parameter_count with
  | 0 => pred
  | .succ n' =>
    fun (param_list : Vector T n') =>
      ∀ (x : T), pred (
        (Vector.mk (#[x].append (param_list.toArray))
          (by
            simp
            apply add_comm
          )
        )
      )

  def curry_pred_try3 {T : Type} {parameter_count : Nat} (pred : Vector T parameter_count → Prop)
  : Vector T 0 → Prop :=
  match parameter_count with
  | 0 => pred
  | .succ n' =>
    curry_pred_try3
      fun (param_list : Vector T n') =>
        ∀ (x : T), pred (
          (Vector.mk (#[x].append (param_list.toArray))
            (by
              simp
              apply add_comm
            )
          )
        )

  def curry_pred_try4
    {T : Type}
    {parameter_count : Nat}
    (pred : Vector T parameter_count → Prop)
    (quant_type : Shared.quant)
    (disj : Bool := false) --
    : Vector T 0 → Prop :=
    match parameter_count with
    | 0 => pred
    | .succ n' =>
      if disj then
        curry_pred_try4
          (fun (param_list : Vector T n') =>
            ∀ (x : T),
              ((param_list.toList.concat x).Nodup) →
              ( pred (
                (Vector.mk (#[x].append (param_list.toArray))
                  (by
                    simp
                    apply add_comm
                  )
                )
              )
            )
          )
          quant_type
      else
        curry_pred_try4
          (fun (param_list : Vector T n') =>
            ∀ (x : T),
              ( pred (
                (Vector.mk (#[x].append (param_list.toArray))
                  (by
                    simp
                    apply add_comm
                  )
                )
              )
            )
          )
          quant_type

def Term.eval
  {R : Type}
  [TupleSet R]
  {tt : TyTy}
  {ty : @Ty R _ tt}
  (t : @Term R _ _ ty)
  : ty.eval :=
    match t with

    | .global_rel_var r _ => r
    | .local_rel_var r => r

    /- binary expression operators -/
    | .intersect r1 r2 => (r1.eval) & (r2.eval)
    | .union r1 r2 => HAdd.hAdd (r1.eval) (r2.eval)
    | .difference r1 r2 => (r1.eval) - (r2.eval)
    | .overwrite r1 r2 => (r1.eval) ++ (r2.eval)
    | .domain_restriction r1 r2 => (r1.eval) <: (r2.eval)
    | .range_restriction r1 r2 => (r1.eval) :> (r2.eval)
    | .dotjoin r1 r2 => (r1.eval) ⋈ (r2.eval)

    /- unary expression operators -/
    | .transclos r => ^ (r.eval)
    | .reflexive_closure  r => * (r.eval)
    | .transposition r => ~ (r.eval)

    /- expression if else -/
    | .if_then_else f r1 r2 => HIfThenElse.hIfThenElse (f.eval) (r1.eval) (r2.eval)

    | .bracket t => t.eval
    | .pred_def _ t => t.eval
    | .fun_def _ t => t.eval
    -- | .marker _ t => t.eval
    -- | .name _ t => t.eval

    | @Term.lam R _ _ _ t f => λ (x : Rel t) => (f x).eval
    | .app f r => f.eval r.eval

    | .q_group m disj p =>
      let predBody := p.eval -- give eval that it is disj (if it is quanto) ? then give the names ?
      if !disj then
        predBody
      else
        predBody

    | @Term.pred R _ arity rel_type parameter_count quantor disj function =>
      let bb := fun (x : Vector (Rel rel_type) parameter_count ) => (function x).eval
      bb

    | .pred_o _ f => fun x => (f x).eval

    | .bind quantor disj function =>
      (curry_pred_try4 (function.eval) quantor disj) Vector0

    | .bind_o quantor_type f =>
      let function := f.eval
      match quantor_type with
        | .all => ∀ x, function x
        | .some => ∃ x, function x
        | .no => ¬ (∃ x, function x)
        | .lone =>
          ∀ x y, (function x) → (function y) → (x = y)
        | .one =>
          (∃ x, function x) ∧ (∀ x y, (function x) → (function y) → (x = y))

    | .number z => z

    /- algebra expression unary operation -/
    | .negation z => - (z.eval)

    /- algebra expression binary operation -/
    | .add z1 z2 => (z1.eval) + (z2.eval)
    | .sub z1 z2 => (z1.eval) - (z2.eval)
    | .div z1 z2 => (z1.eval) / (z2.eval)
    | .mul z1 z2 => (z1.eval) * (z2.eval)
    | .rem z1 z2 => (z1.eval) % (z2.eval)

    /- algebra expression card operation (rel operation)-/
    | .card r => Card.card (r.eval)

    /- formula unary rel bool operator-/
    | .no r => SetMultPredicates.no (r.eval)
    | .one r => SetMultPredicates.one (r.eval)
    | .lone r => SetMultPredicates.lone (r.eval)
    | .some r => SetMultPredicates.some (r.eval)

    /- formula unary logic operator -/
    | .not f => ¬ (f.eval)

    /- formula binary logic operator -/
    | .or f1 f2 => (f1.eval) ∨ (f2.eval)
    | .and f1 f2 => (f1.eval) ∧ (f2.eval)
    | .implication f1 f2 => (f1.eval) → (f2.eval)
    | .equivalent f1 f2 => (f1.eval) = (f2.eval)

    /- formula if else -/
    | .f_if_then_else f1 f2 f3 =>
      ((f1.eval) -> (f2.eval)) ∧ (¬ (f1.eval) → (f2.eval))

    /- formula algebraic comparison operator -/
    | .algebraic_leq z1 z2 => (z1.eval) <= (z2.eval)
    | .algebraic_geq z1 z2 => (z1.eval) >= (z2.eval)
    | .algebraic_lt z1 z2 => (z1.eval) < (z2.eval)
    | .algebraic_gt z1 z2 => (z1.eval) > (z2.eval)
    | .algebraic_eq z1 z2 => (z1.eval) = (z2.eval)

    /- formula relation comparison operation -/
    | .in r1 r2 => (r1.eval) ⊂ (r2.eval)
    | .eq r1 r2 => (r1.eval) ≡ (r2.eval)
    | .neq r1 r2 => (r1.eval) ≢  (r2.eval)

    | type t => t

    -- | q_group {t : RelType R n} {ran : Ty (.isPred t)}
    --     : Shared.quant →
    --       Term ran →
    --       Term .formula

  -- instance {R : Type} [TupleSet R] {ty : @Ty R _} (t : @Term R _ ty):
  --   CoeDep (@Term R _ ty) t ty.eval where
  --     coe := t.eval

  -- instance {R : Type} [TupleSet R] {n : ℕ} (t : @Term R _ (Ty.type n)):
  --   CoeDep _ t Type where
  --     coe := Rel t.eval

end ThoR.Semantics

-- /-
-- all disj x, y, z : r | ...

-- ->
-- all disj x : r | all y : r | all z : r | ...


-- -/
-- open ThoR.Semantics
-- open ThoR

-- -- automatic coercion from t : RelType to Rel t : Type
-- instance {R : Type} [ThoR.TupleSet R] {n : ℕ} (t : RelType R n):
--   CoeDep (RelType R n ) t Type where
--     coe := ThoR.Rel t

-- variable (R : Type) [TupleSet R]
-- #check ThoR.Rel (RelType.mk.sig R Shared.mult.set)

-- class vars (R : Type) [TupleSet R] where
--   UNIV : ((RelType.mk.sig R Shared.mult.set) : Type)
--   Time : Rel (RelType.mk.sig R Shared.mult.set)

-- variable (ThoR_TupleSet : Type) [TupleSet ThoR_TupleSet] [vars ThoR_TupleSet]

-- @[default_instance]
-- instance : ThoR.TupleSet ThoR_TupleSet := by sorry

-- @[default_instance]
-- instance : vars ThoR_TupleSet := by sorry

-- /-
-- pred_in1 [x : set univ] {
--  x in x
-- }
-- -/
-- def pred_in1 :=
--   Term.pred_def "p1" (
--   -- @Term.marker ThoR_TupleSet _ [] _ Marker.alloy_predicate (
--   --   @Term.name ThoR_TupleSet _ _ _ "pred_in1" (
--       Term.lam _ (
--         λ (r : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--           Term.in
--             (expression1 := Term.local_rel_var r)
--             (expression2 := Term.local_rel_var r)
--       )
--       )

-- /-
-- pred_in2 [x : set univ] {
--   x in m/UNIV
-- }
-- -/
-- def pred_in2 :=
--   Term.pred_def "p2" (
--     Term.lam _ (
--       λ (x : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--         Term.in
--           (expression1 := Term.local_rel_var x)
--           (expression2 := Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "m/UNIV")
--     )
--   )

-- #check (pred_in1 ThoR_TupleSet)
-- #check (
--   Term.app
--     (pred_in1 ThoR_TupleSet)
--     (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")
--   ).eval

-- -- pred_in1[univ]
-- example : (Term.app (pred_in1 ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval := by
--   dsimp [Term.eval]
--   apply Set.subset_refl

-- -- pred_in2[univ]
-- example : (
--   Term.app
--     (pred_in2 ThoR_TupleSet)
--     (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "m/UNIV")
--   ).eval := by
--   dsimp [Term.eval]
--   apply Set.subset_refl

-- /-
-- pred_in3 [x : set univ, y : set univ] {
--   x in y
-- }
-- -/
-- def pred_in3 :=
--   Term.pred_def "p3" (
--     Term.lam _ (
--       λ (x : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--         Term.lam _ (
--           λ (y : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--             Term.in
--               (expression1 := Term.local_rel_var x)
--               (expression2 := Term.local_rel_var y)
--         )
--     )
--   )

-- -- pred_in3[univ,univ]
-- example : (
--   Term.app
--     (Term.app
--       (@pred_in3 ThoR_TupleSet _)
--       (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "m/UNIV")
--     )
--     (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "m/UNIV")
--   ).eval := by
--     dsimp [Term.eval]
--     apply Set.subset_refl

-- /-
-- fun1 [x : set univ, y : set univ] : univ {
--   x & y
-- }
-- -/
-- def fun1 :=
--   Term.fun_def "f1" (
--     Term.lam _ (
--       λ (x : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--         Term.lam _ (
--           λ (y : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--             Term.intersect
--               (Term.local_rel_var x)
--               (Term.local_rel_var y)
--         )
--     )
--   )

-- /-
-- fun2 [r : set univ] : univ {
--   fun1 r
-- }
-- -/
-- def fun2 :=
--   Term.fun_def "f2" (
--     Term.lam _ (
--       λ (r : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--         ( Term.app
--           (Term.app
--             (fun1 ThoR_TupleSet) (Term.local_rel_var r)
--           )
--           (Term.local_rel_var r))
--     )
--   )

-- /-
-- fun1 [r : set univ] : univ {
--   r + r
-- }
-- -/
-- def fun_union1 :=
--     Term.lam _ (
--       λ (r : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--         Term.union
--           (Term.local_rel_var r)
--           (Term.local_rel_var r)
--     )

-- #check (Term.app (fun_union1 ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval
-- -- pred_in1[univ]
-- example : (Term.app (fun_union1 ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval =  (@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _) := by
--   dsimp [Term.eval]

-- /-
-- fun1 [r : set univ] : univ {
--   fun_union1 r + fun_union1 r
-- }
-- -/
-- def fun_union_union :=
--     Term.lam _ (
--       λ (r : (Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set))) =>
--         Term.union
--           (Term.app (fun_union1 ThoR_TupleSet) (Term.local_rel_var r))
--           (Term.app (fun_union1 ThoR_TupleSet) (Term.local_rel_var r))
--     )
-- #check (Term.app (fun_union_union ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval


-- -- set_option diagnostics true
-- example : (Term.app (fun_union_union ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval = ((@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _)) + ((@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _)) := by
-- --  unfold Term.eval
--   dsimp [Term.eval]

-- #check Term.union (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV") (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")

-- #check Term.union (Term.union (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV") (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")) (Term.union (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV") (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV"))

-- example : (Term.app (fun_union_union ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval = (Term.union (Term.union (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV") (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")) (Term.union (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV") (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV"))).eval := by
--   dsimp [Term.eval]

-- example : (Term.app (fun_union_union ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval ≡ ((@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _)) + ((@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _)) := by
--   dsimp [Term.eval]
--   dsimp [HEqual.hEqual]

-- example : (Term.app (fun_union_union ThoR_TupleSet) (Term.global_rel_var (@vars.UNIV ThoR_TupleSet _ _) "UNIV")).eval ≡ (@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _) + (@vars.UNIV ThoR_TupleSet _ _) := by
--   dsimp [Term.eval]
--   -- TODO apply rewrite-lemma for associativity of +
--   dsimp [HEqual.hEqual]
--   sorry
