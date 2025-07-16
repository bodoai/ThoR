
/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

inductive TyTy : Type 1 where
  | isTy
  | isPred
    (parameter_count : Nat)
    : TyTy

-- construction follows https://lean-lang.org/documentation/examples/debruijn/
  inductive Ty : (tt : TyTy) → Type u where
    | expression : Ty .isTy-- Rel rel_type
    | formula : Ty .isTy -- Prop
    | pred :
      (parameter_count : Nat) →
      Ty (.isPred parameter_count)

  @[reducible]
  def Ty.eval {tt : TyTy} (ty : Ty tt) : Type :=
    match ty with
    | .expression => Nat
    | .formula => Prop
    | .pred n => Vector Nat n → Prop


  inductive Term
    : (ty : Ty.{u} tt) →
      Type (u+1)
      where

    | toExpr (n : Nat) : Term .expression

    | eq
      : (expression1 : Term .expression) →
        (expression2 : Term .expression) →
        Term .formula

    | pred
      {parameter_count : Nat}
      :
      (function :
        (Vector Nat parameter_count) →
        Term .formula
      ) →
      Term (.pred parameter_count)

    | bind
      {parameter_count : Nat}
      : (pred : Term (.pred parameter_count) ) →
        Term .formula

    -- | type {n : ℕ} (t : RelType R n) : Term (.type n)


#check Term.pred
          (λ (parameter_vector : (Vector Nat 2)) => Term.eq
              (expression1 := Term.toExpr (parameter_vector.get 0))
              (expression2 := Term.toExpr (parameter_vector.get 0)) )

#check Term.bind
        (Term.pred
          (λ (parameter_vector : (Vector Nat 2)) => Term.eq
              (expression1 := Term.toExpr (parameter_vector.get 0))
              (expression2 := Term.toExpr (parameter_vector.get 0)) )
        )
def Vector0 {T : Type} : Vector T 0:= #[].toVector

def quantify_predicate
  {T : Type}
  {parameter_count : Nat}
  (pred : Vector T parameter_count → Prop)
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
              apply Nat.add_comm
            )
          )
        )

      let part :=
            (fun (param_list : Vector T n') =>
              ∀ (x : T), function x param_list
            )

      quantify_predicate part

def Term.eval
  {tt : TyTy}
  {ty : Ty tt}
  (t : Term ty)
  : ty.eval :=
    match t with

    | .toExpr n => n

    | @Term.pred parameter_count function =>
      fun (x : Vector Nat parameter_count ) =>
      (function x).eval

    | @Term.bind parameter_count function =>
      let new_function :=
        (fun (pv : Vector Nat parameter_count) =>
          (function.eval) pv)

      let result := quantify_predicate new_function

      result

    | .eq e1 e2 => (e1.eval) = (e2.eval)



  def  p1
    :=
    (  Term.bind
        (  Term.pred
          (  fun  (  parameter_vector  : Vector.{0} Nat 1)
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
          (  fun  (  parameter_vector  : Vector.{0} Nat 2)
            =>
            (  Term.eq
              (  Term.toExpr  (parameter_vector.get 0)  )
              (  Term.toExpr  (parameter_vector.get 1)  )
            )
          )
        )
      )

theorem theorem1 : p1.eval = p2.eval := by
  unfold p1
  unfold p2
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
