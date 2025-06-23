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
  | isPred {R : Type} [TupleSet R] (t : RelType R n): TyTy

-- construction follows https://lean-lang.org/documentation/examples/debruijn/
  inductive Ty {R : Type} [TupleSet R] : (tt : TyTy) → Type u where
    | number : Ty .isTy-- ℤ
    | formula : Ty .isTy -- Prop
    | expression : {n : ℕ} → (rel_type : RelType R n) → Ty .isTy-- Rel rel_type
    | function : {n : ℕ} → (t : RelType R n) → Ty .isTy → Ty .isTy -- type1.eval → type2.eval
--    | pred : {n : ℕ} → {t : RelType R n} → Ty (.isPred t) → Ty .isTy
    | pred_1 : {n : ℕ} → (t : RelType R n) → Ty (.isPred t)
    | pred_n : {n : ℕ} → (t : RelType R n) → Ty (.isPred t) → Ty (.isPred t)

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
  --  | .pred p => p.eval
    | .pred_1 dom_rel_type => Rel dom_rel_type → Prop
    | .pred_n dom_rel_type p' => Rel dom_rel_type → (p'.eval)


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

    -- /- expression constants -/
    -- --| univ
    -- --| none
    -- --| iden

    -- /- binary expression operators -/
    -- | union
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 + t2))

    -- | intersect
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 & t2))

    -- | difference
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 - t2))

    -- | overwrite
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 ++ t2))

    -- | domain_restriction
    --   {n : ℕ}
    --   {t1 : RelType R 1}
    --   {t2 : RelType R n}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 <: t2))

    -- | range_restriction
    --   {n : ℕ}
    --   {t1 : RelType R n}
    --   {t2 : RelType R 1}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 :> t2))

    -- | dotjoin
    --   {n m : ℕ}
    --   {t1 : RelType R (n+1)}
    --   {t2 : RelType R (m+2)}
    --   : Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (t1 ⋈ t2))

    -- /- unary expression operators -/
    -- | transclos
    --   {t : RelType R 2}
    --   : Term (.expression t) →
    --     Term (.expression (^ t))

    -- | reflexive_closure
    --   {t : RelType R 2}
    --   : Term (.expression t) →
    --     Term (.expression (* t))

    -- | transposition
    --   {t : RelType R 2}
    --   : Term (.expression t) →
    --     Term (.expression (~ t))

    -- /- expression if else -/
    -- | if_then_else
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : Term .formula →
    --     Term (.expression t1) →
    --     Term (.expression t2) →
    --     Term (.expression (RelType.ifThenElse t1 t2))

    -- /- function call from expression ? -/
    -- --| call -- skip ?

    -- /--bracket definition-/
    -- | bracket : Term ty → Term ty

    -- /--predicate definition-/
    -- | pred_def (name : String) : Term ty → Term ty

    -- /--function definition-/
    -- | fun_def (name : String) : Term ty → Term ty
    -- -- | marker : Marker → Term ty → Term ty
    -- -- | name : String → Term ty → Term ty

    -- /- algebra expression number -/
    -- | number (z : ℤ) : Term .number -- may have to be from N

    -- /- algebra expression unary operation -/
    -- | negation : Term .number → Term .number

    -- /- algebra expression binary operation -/
    -- | add
    --   : Term .number →
    --   Term .number →
    --   Term .number

    -- | sub
    --   : Term .number →
    --   Term .number →
    --   Term .number

    -- | mul
    --   : Term .number →
    --     Term .number →
    --     Term .number

    -- | div
    --   : Term .number →
    --     Term .number →
    --     Term .number

    -- | rem
    --   : Term .number →
    --     Term .number →
    --     Term .number

    -- /- algebra expression card operation (rel operation)-/
    -- | card
    --   {n : ℕ}
    --   {t : RelType R n}
    --   : Term (.expression t) →
    --     Term .number

    -- /- formula unary rel bool operator-/
    -- | no
    --   {n : ℕ}
    --   {t : RelType R n}
    --   : Term (.expression t) →
    --     Term .formula

    -- | one
    --   {n : ℕ}
    --   {t : RelType R n}
    --   : Term (.expression t) →
    --     Term .formula

    -- | lone
    --   {n : ℕ}
    --   {t : RelType R n}
    --   : Term (.expression t) →
    --     Term .formula

    -- | some
    --   {n : ℕ}
    --   {t : RelType R n}
    --   : Term (.expression t) →
    --     Term .formula

    -- /- formula unary logic operator -/
    -- | not : Term .formula → Term .formula

    -- /- formula binary logic operator -/
    -- | or
    --   : Term .formula →
    --     Term .formula →
    --     Term .formula

    -- | and
    --   : Term .formula →
    --     Term .formula →
    --     Term .formula

    -- | implication
    --   : Term .formula →
    --     Term .formula →
    --     Term .formula

    -- | equivalent
    --   : Term .formula →
    --     Term .formula →
    --     Term .formula

    -- /- formula if else-/
    -- | f_if_then_else
    --   : Term .formula →
    --     Term .formula →
    --     Term .formula →
    --     Term .formula

    -- /- formula algebraic comparison operator -/
    -- | algebraic_leq
    --   : Term .number →
    --     Term .number →
    --     Term .formula

    -- | algebraic_geq
    --   : Term .number →
    --     Term .number →
    --     Term .formula

    -- | algebraic_eq
    --   : Term .number →
    --     Term .number →
    --     Term .formula

    -- | algebraic_lt
    --   : Term .number →
    --     Term .number →
    --     Term .formula

    -- | algebraic_gt
    --   : Term .number →
    --     Term .number →
    --     Term .formula

    /- formula relation comparison operation -/
    | in
      {n : ℕ}
      {t1 t2 : RelType R n}
      : (expression1 : Term (.expression t1)) →
        (expression2 : Term (.expression t2)) →
        Term .formula

    -- | eq
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : (expression1 : Term (.expression t1)) →
    --     (expression2 : Term (.expression t2)) →
    --     Term .formula

    -- | neq
    --   {n : ℕ}
    --   {t1 t2 : RelType R n}
    --   : (expression1 : Term (.expression t1)) →
    --     (expression2 : Term (.expression t2)) →
    --     Term .formula

    -- /- function abstraction -/
    -- | lam (t : RelType R n)
    --   : (Rel t → Term ran) →
    --     Term (.function t ran)

    -- /- function application / application of argument to call ? -/
    -- | app
    --   : Term (.function t ran) →
    --     Term (.expression t) →
    --     Term ran

    | q_group
      : Shared.quant →
        Term .formula →
        Term .formula

    | pred_1 {n : ℕ} {t : RelType R n}
      : (Rel t → Term .formula) →
        Term (Ty.pred_1 t)
    | pred_n {n : ℕ} {t : RelType R n} {ran : Ty (.isPred t)}
      : (Rel t → Term ran) →
        Term (Ty.pred_n t ran)

    | bind_1 {t : RelType R n}
      : (m : Shared.quant) →
        (unary_pred : Term (Ty.pred_1 t)) →
        (parameter : Term (.expression t)) →
        Term .formula
    | bind_n {t : RelType R n} {ran : Ty (.isPred t)}
      : (m : Shared.quant) →
        (nary_pred : Term (Ty.pred_n t ran)) →
        (parameter : Term (.expression t)) →
        Term ran


variable {R : Type} [TupleSet R] (t : RelType R n)
#check Term.pred_1 (λ (r : Rel t) => Term.in
              (expression1 := Term.local_rel_var r)
              (expression2 := Term.local_rel_var r) )
#check Term.pred_n (
    λ (q : Rel t) => Term.pred_1 (
      λ (r : Rel t) =>
        Term.in
          (expression1 := Term.local_rel_var q)
          (expression2 := Term.local_rel_var r)
      )
)

def p1 := Term.pred_n (
    λ (q : Rel t) => Term.pred_1 (
      λ (r : Rel t) =>
        Term.in
          (expression1 := Term.local_rel_var q)
          (expression2 := Term.local_rel_var r)
      )
)


#check (p1 t)

-- set_option diagnostics true
-- set_option diagnostics.threshold 0

example : p1 t = Term.pred_n (
    λ (q : Rel t) => Term.pred_1 (
      λ (r : Rel t) =>
        Term.in
          (expression1 := Term.local_rel_var q)
          (expression2 := Term.local_rel_var r)
      )
) := by
  sorry



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
      --| .intersect r1 r2 => (r1.eval) & (r2.eval)
      --| .union r1 r2 => HAdd.hAdd (r1.eval) (r2.eval)
      --| .difference r1 r2 => (r1.eval) - (r2.eval)
      --| .overwrite r1 r2 => (r1.eval) ++ (r2.eval)
      --| .domain_restriction r1 r2 => (r1.eval) <: (r2.eval)
      --| .range_restriction r1 r2 => (r1.eval) :> (r2.eval)
      --| .dotjoin r1 r2 => (r1.eval) ⋈ (r2.eval)

      /- unary expression operators -/
      --| .transclos r => ^ (r.eval)
      --| .reflexive_closure  r => * (r.eval)
      --| .transposition r => ~ (r.eval)

      /- expression if else -/
      --| .if_then_else f r1 r2 => HIfThenElse.hIfThenElse (f.eval) (r1.eval) (r2.eval)

      --| .bracket t => t.eval
      --| .pred_def _ t => t.eval
      --| .fun_def _ t => t.eval
      -- | .marker _ t => t.eval
      -- | .name _ t => t.eval

      --| @Term.lam R _ _ _ t f => λ (x : Rel t) => (f x).eval
      --| .app f r => f.eval r.eval

      | .q_group m p => p.eval

      | .pred_1 f =>
        let result := λ x => (f x).eval
        result

      | @Term.pred_n R _ n t ran f =>
        let result := ( λ x => (f x).eval : Rel t → ran.eval )
        result

      | @Term.bind_1 R _ _ t m f parameter =>
        let function := f.eval
        let param := parameter.eval -- unused currently ?
        let result := ∀ x, function x
        result

      | @Term.bind_n R _ arity relType range quantifier term parameter =>
        let test1 := @Term.eval R _ tt ty t
        let test2 := parameter.eval

        let function := term.eval
        let param := parameter.eval

        /-possible problem? : cant use ∀ outside of prop ?-/
        let result := (function param : range.eval)
        result


      --| .number z => z

      /- algebra expression unary operation -/
      --| .negation z => - (z.eval)

      /- algebra expression binary operation -/
      --| .add z1 z2 => (z1.eval) + (z2.eval)
      --| .sub z1 z2 => (z1.eval) - (z2.eval)
      --| .div z1 z2 => (z1.eval) / (z2.eval)
      --| .mul z1 z2 => (z1.eval) * (z2.eval)
      --| .rem z1 z2 => (z1.eval) % (z2.eval)

      /- algebra expression card operation (rel operation)-/
      --| .card r => Card.card (r.eval)

      /- formula unary rel bool operator-/
      -- | .no r => SetMultPredicates.no (r.eval)
      -- | .one r => SetMultPredicates.one (r.eval)
      -- | .lone r => SetMultPredicates.lone (r.eval)
      -- | .some r => SetMultPredicates.some (r.eval)

      /- formula unary logic operator -/
      -- | .not f => ¬ (f.eval)

      /- formula binary logic operator -/
      -- | .or f1 f2 => (f1.eval) ∨ (f2.eval)
      -- | .and f1 f2 => (f1.eval) ∧ (f2.eval)
      -- | .implication f1 f2 => (f1.eval) → (f2.eval)
      -- | .equivalent f1 f2 => (f1.eval) = (f2.eval)

      /- formula if else -/
      -- | .f_if_then_else f1 f2 f3 =>
      --   ((f1.eval) -> (f2.eval)) ∧ (¬ (f1.eval) → (f2.eval))

      /- formula algebraic comparison operator -/
      -- | .algebraic_leq z1 z2 => (z1.eval) <= (z2.eval)
      -- | .algebraic_geq z1 z2 => (z1.eval) >= (z2.eval)
      -- | .algebraic_lt z1 z2 => (z1.eval) < (z2.eval)
      -- | .algebraic_gt z1 z2 => (z1.eval) > (z2.eval)
      -- | .algebraic_eq z1 z2 => (z1.eval) = (z2.eval)

      /- formula relation comparison operation -/
      | .in r1 r2 => (r1.eval) ⊂ (r2.eval)
      -- | .eq r1 r2 => (r1.eval) ≡ (r2.eval)
      -- | .neq r1 r2 => (r1.eval) ≢  (r2.eval)

      -- | q_group {t : RelType R n} {ran : Ty (.isPred t)}
      --     : Shared.quant →
      --       Term ran →
      --       Term .formula

--   instance {R : Type} [TupleSet R] {ty : @Ty R _} (t : @Term R _ ty):
--     CoeDep (@Term R _ ty) t ty.eval where
--       coe := t.eval

--   instance {R : Type} [TupleSet R] {n : ℕ} (t : @Term R _ (Ty.type n)):
--     CoeDep _ t Type where
--       coe := Rel t.eval

-- end ThoR.Semantics

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
