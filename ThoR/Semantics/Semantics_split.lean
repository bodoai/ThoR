
/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Relation.Rel
import ThoR.Shared.Syntax.quant

import ThoR.Basic

open ThoR

inductive TyTy : Type 1 where
  | isTy
  | isPred
    {arity : Nat}
    {R : Type}
    [ThoR.TupleSet R]
    (rel_type : ThoR.RelType R arity)
    (parameter_count : Nat)
    : TyTy

-- construction follows https://lean-lang.org/documentation/examples/debruijn/
  inductive Ty {R : Type} [ThoR.TupleSet R] : (tt : TyTy) → Type u where
    | number : Ty .isTy-- ℤ
    | expression : {n : ℕ} → (rel_type : ThoR.RelType R n) → Ty .isTy-- Rel rel_type
    | formula : Ty .isTy -- Prop
    | pred :
      {arity : Nat} →
      (rel_type : ThoR.RelType R arity) →
      (parameter_count : Nat) →
      Ty (.isPred rel_type parameter_count)

  @[reducible]
  def Ty.eval {R : Type} [ThoR.TupleSet R] {tt : TyTy} (ty : @Ty R _ tt) : Type :=
    match ty with
    | .number => ℤ
    | .expression rel_type => ThoR.Rel rel_type
    | .formula => Prop
    | .pred rel_type n => Vector (ThoR.Rel rel_type) n → Prop

  inductive AlgebraTerm
    {R : Type}
    [ThoR.TupleSet R]
    : {tt : TyTy} → (ty : @Ty.{u} R _ tt) →
      Type (u+1)
      where
      /- algebra expression number -/
      | number (z : ℤ) : AlgebraTerm .number -- may have to be from N

      /- algebra expression unary operation -/
      | negation : AlgebraTerm .number → AlgebraTerm .number

      /- algebra expression binary operation -/
      | add
        : AlgebraTerm .number →
        AlgebraTerm .number →
        AlgebraTerm .number

      | sub
        : AlgebraTerm .number →
        AlgebraTerm .number →
        AlgebraTerm .number

      | mul
        : AlgebraTerm .number →
          AlgebraTerm .number →
          AlgebraTerm .number

      | div
        : AlgebraTerm .number →
          AlgebraTerm .number →
          AlgebraTerm .number

      | rem
        : AlgebraTerm .number →
          AlgebraTerm .number →
          AlgebraTerm .number

      /- algebra expression card operation (rel operation)-/
      | card
        {n : ℕ}
        {t : RelType R n}
        : AlgebraTerm (.expression t) →
          AlgebraTerm .number

  mutual
    inductive ExpressionTerm
      {R : Type}
      [ThoR.TupleSet R]
      : {tt : TyTy} → (ty : @Ty.{u} R _ tt) →
        Type (u+1)
        where
        | global_rel_var
          {n : ℕ} {t : RelType R n}
          (r : Rel t) (name : String): ExpressionTerm (.expression t)

        | local_rel_var
          {n : ℕ} {t : RelType R n}
          (r : Rel t): ExpressionTerm (.expression t)

        | toExpr
          {n : ℕ} {t : ThoR.RelType R n}
          (r : ThoR.Rel t) : ExpressionTerm (.expression t)

        /- binary expression operators -/
        | union
          {n : ℕ}
          {t1 t2 : RelType R n}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 + t2))

        | intersect
          {n : ℕ}
          {t1 t2 : RelType R n}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 & t2))

        | difference
          {n : ℕ}
          {t1 t2 : RelType R n}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 - t2))

        | overwrite
          {n : ℕ}
          {t1 t2 : RelType R n}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 ++ t2))

        | domain_restriction
          {n : ℕ}
          {t1 : RelType R 1}
          {t2 : RelType R n}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 <: t2))

        | range_restriction
          {n : ℕ}
          {t1 : RelType R n}
          {t2 : RelType R 1}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 :> t2))

        | dotjoin
          {n m : ℕ}
          {t1 : RelType R (n+1)}
          {t2 : RelType R (m+2)}
          : ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (t1 ⋈ t2))

        /- unary expression operators -/
        | transclos
          {t : RelType R 2}
          : ExpressionTerm (.expression t) →
            ExpressionTerm (.expression (^ t))

        | reflexive_closure
          {t : RelType R 2}
          : ExpressionTerm (.expression t) →
            ExpressionTerm (.expression (* t))

        | transposition
          {t : RelType R 2}
          : ExpressionTerm (.expression t) →
            ExpressionTerm (.expression (~ t))

        /- expression if else -/
        | if_then_else
          {n : ℕ}
          {t1 t2 : RelType R n}
          : FormulaTerm .formula →
            ExpressionTerm (.expression t1) →
            ExpressionTerm (.expression t2) →
            ExpressionTerm (.expression (RelType.ifThenElse t1 t2))

    inductive FormulaTerm
    {R : Type}
    [ThoR.TupleSet R]
    : {tt : TyTy} → (ty : @Ty.{u} R _ tt) →
      Type (u+1)
      where
      /- formula unary rel bool operator-/
      | no
        {n : ℕ}
        {t : RelType R n}
        : ExpressionTerm (.expression t) →
          FormulaTerm .formula

      | one
        {n : ℕ}
        {t : RelType R n}
        : ExpressionTerm (.expression t) →
          FormulaTerm .formula

      | lone
        {n : ℕ}
        {t : RelType R n}
        : ExpressionTerm (.expression t) →
          FormulaTerm .formula

      | some
        {n : ℕ}
        {t : RelType R n}
        : ExpressionTerm (.expression t) →
          FormulaTerm .formula

      /- formula unary logic operator -/
      | not : FormulaTerm .formula → FormulaTerm .formula

      /- formula binary logic operator -/
      | or
        : FormulaTerm .formula →
          FormulaTerm .formula →
          FormulaTerm .formula

      | and
        : FormulaTerm .formula →
          FormulaTerm .formula →
          FormulaTerm .formula

      | implication
        : FormulaTerm .formula →
          FormulaTerm .formula →
          FormulaTerm .formula

      | equivalent
        : FormulaTerm .formula →
          FormulaTerm .formula →
          FormulaTerm .formula

      /- formula if else-/
      | f_if_then_else
        : FormulaTerm .formula →
          FormulaTerm .formula →
          FormulaTerm .formula →
          FormulaTerm .formula

      /- formula algebraic comparison operator -/
      | algebraic_leq
        : AlgebraTerm (R := R) .number →
          AlgebraTerm (R := R) .number →
          FormulaTerm .formula

      | algebraic_geq
        : AlgebraTerm (R := R) .number →
          AlgebraTerm (R := R) .number →
          FormulaTerm .formula

      | algebraic_eq
        : AlgebraTerm (R := R) .number →
          AlgebraTerm (R := R) .number →
          FormulaTerm .formula

      | algebraic_lt
        : AlgebraTerm (R := R) .number →
          AlgebraTerm (R := R) .number →
          FormulaTerm .formula

      | algebraic_gt
        : AlgebraTerm (R := R) .number →
          AlgebraTerm (R := R) .number →
          FormulaTerm .formula

      /- formula relation comparison operation -/
      | in
        {n : ℕ}
        {t1 t2 : RelType R n}
        : (expression1 : ExpressionTerm (.expression t1)) →
          (expression2 : ExpressionTerm (.expression t2)) →
          FormulaTerm .formula

      | eq
        {n : ℕ}
        {t1 t2 : ThoR.RelType R n}
        : (expression1 : ExpressionTerm (.expression t1)) →
          (expression2 : ExpressionTerm (.expression t2)) →
          FormulaTerm .formula

      | neq
        {n : ℕ}
        {t1 t2 : RelType R n}
        : (expression1 : ExpressionTerm (.expression t1)) →
          (expression2 : ExpressionTerm (.expression t2)) →
          FormulaTerm .formula

      | pred
        {arity : Nat}
        {rel_type : ThoR.RelType R arity}
        {parameter_count : Nat}
        :
        (function :
          (Vector (ThoR.Rel rel_type) parameter_count) →
          FormulaTerm .formula
        ) →
        FormulaTerm (.pred rel_type parameter_count)

      | bind
        {arity : Nat}
        {rel_type : ThoR.RelType R arity}
        {parameter_count : Nat}
        : (pred : FormulaTerm (.pred rel_type parameter_count) ) →
          FormulaTerm .formula
  end

  inductive Term
    {R : Type}
    [ThoR.TupleSet R]
    : {tt : TyTy} → (ty : @Ty.{u} R _ tt) →
      Type (u+1)
      where

    | expr : ExpressionTerm ty → Term ty
    | formula : FormulaTerm ty → Term ty

    /--bracket definition-/
    | bracket : Term ty → Term ty

    | pred_def (name : String) : Term ty → Term ty

    /--function definition-/
    | fun_def (name : String) : Term ty → Term ty
    -- | marker : Marker → Term ty → Term ty
    -- | name : String → Term ty → Term ty

    -- | type {n : ℕ} (t : RelType R n) : Term (.type n)

variable (I : Type) [ThoR.TupleSet I]
instance : ThoR.TupleSet I := by sorry
variable (t : ThoR.RelType I n)

#check FormulaTerm.pred
          (λ (parameter_vector : (Vector (ThoR.Rel t) 2)) => FormulaTerm.eq
              (expression1 := ExpressionTerm.toExpr (parameter_vector.get 0))
              (expression2 := ExpressionTerm.toExpr (parameter_vector.get 0)) )

#check FormulaTerm.bind
        (FormulaTerm.pred
          (λ (parameter_vector : (Vector (ThoR.Rel t) 2)) => FormulaTerm.eq
              (expression1 := ExpressionTerm.toExpr (parameter_vector.get 0))
              (expression2 := ExpressionTerm.toExpr (parameter_vector.get 0)) )
        )
def Vector0 {T : Type} : Vector T 0:= #[].toVector

def quantify_predicate
  {T : Type}
  {parameter_count : Nat}
  (pred : Vector T parameter_count → Prop)
  (quant_type : Shared.quant)
  : Prop :=
  match parameter_count with
    | 0 =>
      pred Vector0
    | .succ n' =>
      let function :=
        fun (x : T) (param_list : Vector T n') => pred (
          (Vector.mk (#[x].append (param_list.toArray))
            (by
              simp
              apply add_comm
            )
          )
        )

      let part :=
        match quant_type with
          | .all =>
            (fun (param_list : Vector T n') =>
              ∀ (x : T), function x param_list
            )

          | .some =>
            (fun (param_list : Vector T n') =>
              ∃ (x : T), function x param_list
            )

          | .no =>
            (fun (param_list : Vector T n') =>
              ∃ (x : T), function x param_list
            )

          | .lone =>
            (fun (param_list : Vector T n') =>
              ∀  (x y : T),
              function x param_list →
              function y param_list →
              (x = y)
            )

          | .one =>
            (fun (param_list : Vector T n') =>
              ( ∃ (x : T), function x param_list ∧
                ∀  (x y : T),
                  function x param_list →
                  function y param_list →
                  (x = y)
              )
            )

      quantify_predicate part quant_type

mutual
  def ExpressionTerm.eval
    {R : Type}
    [ThoR.TupleSet R]
    {tt : TyTy}
    {ty : @Ty R _ tt}
    (t : @ExpressionTerm R _ _ ty)
    : ty.eval :=
      match t with

      | .global_rel_var r _ => r
      | .local_rel_var r => r

      | .toExpr n => n

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

    def FormulaTerm.eval
      {R : Type}
      [ThoR.TupleSet R]
      {tt : TyTy}
      {ty : @Ty R _ tt}
      (t : @FormulaTerm R _ _ ty)
      : ty.eval :=
      match t with
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

        | @FormulaTerm.pred R _ arity rel_type parameter_count function =>
        fun (x : Vector _ parameter_count ) =>
        (function x).eval

        | @FormulaTerm.bind R _ arity rel_type parameter_count function =>
          let new_function :=
            (fun (pv : Vector _ parameter_count) =>
              (function.eval) pv)

          let result := quantify_predicate new_function Shared.quant.all

          result

    def AlgebraTerm.eval
      {R : Type}
      [ThoR.TupleSet R]
      {tt : TyTy}
      {ty : @Ty R _ tt}
      (t : @AlgebraTerm R _ _ ty)
      : ty.eval :=
      match t with
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

  end

  def Term.eval
    {R : Type}
    [ThoR.TupleSet R]
    {tt : TyTy}
    {ty : @Ty R _ tt}
    (t : @Term R _ _ ty)
    : ty.eval :=
    match t with
    | .bracket t => t.eval

    | .expr t => t.eval

    | .formula t => t.eval

    | .pred_def _ t => t.eval

    | .fun_def _ t => t.eval

  def  p1
    :=
    (  FormulaTerm.bind
        (  FormulaTerm.pred
          (  fun  (  parameter_vector  : Vector.{0} (ThoR.Rel t) 1)
            =>
            (  FormulaTerm.eq
              (  ExpressionTerm.toExpr  (parameter_vector.get 0)  )
              (  ExpressionTerm.toExpr  (parameter_vector.get 0)  )
            )
          )
        )
      )


  def  p2
    :=
    (  FormulaTerm.bind
        (  FormulaTerm.pred
          (  fun  (  parameter_vector  : Vector.{0} (ThoR.Rel t) 2)
            =>
            (  FormulaTerm.eq
              (  ExpressionTerm.toExpr  (parameter_vector.get 0)  )
              (  ExpressionTerm.toExpr  (parameter_vector.get 1)  )
            )
          )
        )
      )

#check p1 I t

theorem theorem1 : (p1 I t).eval = (p2 I t).eval := by
  unfold p1
  unfold p2
  unfold FormulaTerm.eval
  unfold FormulaTerm.eval
  simp only [quantify_predicate, Vector.get]
  simp
  apply Iff.intro

  repeat sorry


  -- def junctionOfQuants :=
  --   Term.and
  --   (Term.bind (Shared.quant.all) (disj := false) (#["x","y"].toVector)
  --     (Term.pred
  --       (λ (parameter_vector : (Vector (Rel rel_type) 2)) => Term.in
  --           (expression1 := Term.local_rel_var (parameter_vector.get 0))
  --           (expression2 := Term.local_rel_var (parameter_vector.get 1)) )))
  --   (Term.bind (Shared.quant.all) (disj := false) (#["x","y"].toVector)
  --     (Term.pred
  --       (λ (parameter_vector : (Vector (Rel rel_type) 2)) => Term.in
  --           (expression1 := Term.local_rel_var (parameter_vector.get 0))
  --           (expression2 := Term.local_rel_var (parameter_vector.get 1)) )))

  -- def junctionOfFormsInQuant :=
  --   (Term.bind (Shared.quant.all) (disj := false) (#["x","y"].toVector)
  --     (Term.pred
  --       (λ (parameter_vector : (Vector (Rel rel_type) 2)) =>
  --         Term.and
  --           (Term.in
  --           (expression1 := Term.local_rel_var (parameter_vector.get 0))
  --           (expression2 := Term.local_rel_var (parameter_vector.get 1)) )
  --           (Term.in
  --           (expression1 := Term.local_rel_var (parameter_vector.get 0))
  --           (expression2 := Term.local_rel_var (parameter_vector.get 1)) ))))

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
