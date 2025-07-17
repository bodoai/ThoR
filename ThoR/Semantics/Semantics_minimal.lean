
/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Relation.Rel
import ThoR.Shared.Syntax.quant

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


  inductive Term
    {R : Type}
    [ThoR.TupleSet R]
    : {tt : TyTy} → (ty : @Ty.{u} R _ tt) →
      Type (u+1)
      where

    | global_rel_var {n : ℕ} {t : RelType R n} (r : Rel t) (name : String): Term (.expression t)
    | local_rel_var {n : ℕ} {t : RelType R n} (r : Rel t): Term (.expression t)

    | toExpr {n : ℕ} {t : ThoR.RelType R n} (r : ThoR.Rel t) : Term (.expression t)

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

    | pred_def (name : String) : Term ty → Term ty

    /--function definition-/
    | fun_def (name : String) : Term ty → Term ty
    -- | marker : Marker → Term ty → Term ty
    -- | name : String → Term ty → Term ty

    /- algebra expression number -/
    --| number (z : ℤ) : Term .number -- may have to be from N

    /- algebra expression unary operation -/
    --| negation : Term .number → Term .number

    /- algebra expression binary operation -/
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
      {t1 t2 : ThoR.RelType R n}
      : (expression1 : Term (.expression t1)) →
        (expression2 : Term (.expression t2)) →
        Term .formula

    | pred
      {arity : Nat}
      {rel_type : ThoR.RelType R arity}
      {parameter_count : Nat}
      :
      (function :
        (Vector (ThoR.Rel rel_type) parameter_count) →
        Term .formula
      ) →
      Term (.pred rel_type parameter_count)

    | bind
      {arity : Nat}
      {rel_type : ThoR.RelType R arity}
      {parameter_count : Nat}
      : (pred : Term (.pred rel_type parameter_count) ) →
        Term .formula

    -- | type {n : ℕ} (t : RelType R n) : Term (.type n)


variable (I : Type) [ThoR.TupleSet I]
instance : ThoR.TupleSet I := by sorry
variable (t : ThoR.RelType I n)

#check Term.pred
          (λ (parameter_vector : (Vector (ThoR.Rel t) 2)) => Term.eq
              (expression1 := Term.toExpr (parameter_vector.get 0))
              (expression2 := Term.toExpr (parameter_vector.get 0)) )

#check Term.bind
        (Term.pred
          (λ (parameter_vector : (Vector (ThoR.Rel t) 2)) => Term.eq
              (expression1 := Term.toExpr (parameter_vector.get 0))
              (expression2 := Term.toExpr (parameter_vector.get 0)) )
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

def Term.eval
  {R : Type}
  [ThoR.TupleSet R]
  {tt : TyTy}
  {ty : @Ty R _ tt}
  (t : @Term R _ _ ty)
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

    | .bracket t => t.eval

    | .pred_def _ t => t.eval

    | @Term.pred R _ arity rel_type parameter_count function =>
      fun (x : Vector _ parameter_count ) =>
      (function x).eval

    | @Term.bind R _ arity rel_type parameter_count function =>
      let new_function :=
        (fun (pv : Vector _ parameter_count) =>
          (function.eval) pv)

      let result := quantify_predicate new_function Shared.quant.all

      result

    | .eq e1 e2 => (e1.eval) ≡ (e2.eval)



  def  p1
    :=
    (  Term.bind
        (  Term.pred
          (  fun  (  parameter_vector  : Vector.{0} (ThoR.Rel t) 1)
            =>
            (  Term.eq
              (  Term.toExpr  (parameter_vector.get 0)  )
              (  Term.toExpr  (parameter_vector.get 0)  )
            )
          )
        )
      )


  def  p2
    :=
    (  Term.bind
        (  Term.pred
          (  fun  (  parameter_vector  : Vector.{0} (ThoR.Rel t) 2)
            =>
            (  Term.eq
              (  Term.toExpr  (parameter_vector.get 0)  )
              (  Term.toExpr  (parameter_vector.get 1)  )
            )
          )
        )
      )

#check p1 I t

theorem theorem1 : (p1 I t).eval = (p2 I t).eval := by
  unfold p1
  unfold p2
  unfold Term.eval
  simp only [Term.eval]
  simp only [quantify_predicate]






  sorry


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
