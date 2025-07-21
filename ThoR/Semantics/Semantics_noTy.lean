/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Relation.Rel
import ThoR.Shared.Syntax.quant

namespace ThoR.Semantics

  /-
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
    | function : {n : ℕ} → (t : RelType R n) → Ty .isTy → Ty .isTy
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
    | .function dom_rel_type ran => Rel dom_rel_type → ran.eval
    | .pred rel_type n => Vector (ThoR.Rel rel_type) n → Prop
  -/

  mutual
    inductive AlgebraTerm
      {R : Type}
      [ThoR.TupleSet R]
      where
        /- algebra expression number -/
        | number (z : ℤ) : AlgebraTerm -- may have to be from N

        /- algebra expression unary operation -/
        | negation : AlgebraTerm → AlgebraTerm

        /- algebra expression binary operation -/
        | add
          : AlgebraTerm →
          AlgebraTerm →
          AlgebraTerm

        | sub
          : AlgebraTerm →
          AlgebraTerm →
          AlgebraTerm

        | mul
          : AlgebraTerm →
            AlgebraTerm →
            AlgebraTerm

        | div
          : AlgebraTerm  →
            AlgebraTerm  →
            AlgebraTerm

        | rem
          : AlgebraTerm  →
            AlgebraTerm  →
            AlgebraTerm

        /- algebra expression card operation (rel operation)-/
        | card
          {n : ℕ}
          {t : RelType R n}
          : ExpressionTerm t →
            AlgebraTerm

    inductive ExpressionTerm
      {R : Type}
      [ThoR.TupleSet R]
      : (RelType R n) → Type
      where
        | bracket : ExpressionTerm rt → ExpressionTerm rt

        | global_rel_var
          {n : ℕ} {rt : RelType R n}
          (r : Rel rt) (name : String): ExpressionTerm rt

        | local_rel_var
          {n : ℕ} {rt : RelType R n}
          (r : Rel rt): ExpressionTerm rt

        | toExpr
          {n : ℕ} {rt : ThoR.RelType R n}
          (r : ThoR.Rel rt) : ExpressionTerm rt
        /- binary expression operators -/
        | union
          {n : ℕ}
          {rt1 rt2 : RelType R n}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 + rt2)

        | intersect
          {n : ℕ}
          {rt1 rt2 : RelType R n}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 & rt2)

        | difference
          {n : ℕ}
          {rt1 rt2 : RelType R n}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 - rt2)

        | overwrite
          {n : ℕ}
          {rt1 rt2 : RelType R n}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 ++ rt2)

        | domain_restriction
          {n : ℕ}
          {rt1 : RelType R 1}
          {rt2 : RelType R n}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 <: rt2)

        | range_restriction
          {n : ℕ}
          {rt1 : RelType R n}
          {rt2 : RelType R 1}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 :> rt2)

        | dotjoin
          {n m : ℕ}
          {rt1 : RelType R (n+1)}
          {rt2 : RelType R (m+2)}
          : ExpressionTerm rt1 →
            ExpressionTerm rt2 →
            ExpressionTerm (rt1 ⋈ rt2)

        /- unary expression operators -/
        | transclos
          {rt : RelType R 2}
          : ExpressionTerm rt →
            ExpressionTerm (^rt)

        | reflexive_closure
          {rt : RelType R 2}
          : ExpressionTerm rt  →
            ExpressionTerm (* rt)

        | transposition
          {rt : RelType R 2}
          : ExpressionTerm rt →
            ExpressionTerm (~ rt)

        /- expression if else -/
        | if_then_else
          {n : ℕ}
          {rt1 rt2 : RelType R n}
          : FormulaTerm →
            ExpressionTerm rt1 →
            ExpressionTerm  rt2 →
            ExpressionTerm (RelType.ifThenElse rt1 rt2)

    inductive FormulaTerm
    {R : Type}
    [ThoR.TupleSet R]
    where
      | bracket : FormulaTerm → FormulaTerm

      /- formula unary rel bool operator-/
      | no
        {n : ℕ}
        {rt : RelType R n}
        : ExpressionTerm rt →
          FormulaTerm

      | one
        {n : ℕ}
        {rt : RelType R n}
        : ExpressionTerm rt →
          FormulaTerm

      | lone
        {n : ℕ}
        {rt : RelType R n}
        : ExpressionTerm rt →
          FormulaTerm

      | some
        {n : ℕ}
        {rt : RelType R n}
        : ExpressionTerm rt →
          FormulaTerm

      /- formula unary logic operator -/
      | not : FormulaTerm → FormulaTerm

      /- formula binary logic operator -/
      | or
        : FormulaTerm  →
          FormulaTerm  →
          FormulaTerm

      | and
        : FormulaTerm  →
          FormulaTerm  →
          FormulaTerm

      | implication
        : FormulaTerm  →
          FormulaTerm  →
          FormulaTerm

      | equivalent
        : FormulaTerm  →
          FormulaTerm  →
          FormulaTerm

      /- formula if else-/
      | f_if_then_else
        : FormulaTerm  →
          FormulaTerm  →
          FormulaTerm  →
          FormulaTerm

      /- formula algebraic comparison operator -/
      | algebraic_leq
        : AlgebraTerm   →
          AlgebraTerm  →
          FormulaTerm

      | algebraic_geq
        : AlgebraTerm  →
          AlgebraTerm  →
          FormulaTerm

      | algebraic_eq
        : AlgebraTerm  →
          AlgebraTerm  →
          FormulaTerm

      | algebraic_lt
        : AlgebraTerm  →
          AlgebraTerm  →
          FormulaTerm

      | algebraic_gt
        : AlgebraTerm  →
          AlgebraTerm  →
          FormulaTerm

      /- formula relation comparison operation -/
      | in
        {n : ℕ}
        {rt1 rt2 : RelType R n}
        : (expression1 : ExpressionTerm rt1) →
          (expression2 : ExpressionTerm rt2) →
          FormulaTerm

      | eq
        {n : ℕ}
        {rt1 rt2 : ThoR.RelType R n}
        : (expression1 : ExpressionTerm rt1) →
          (expression2 : ExpressionTerm rt2) →
          FormulaTerm

      | neq
        {n : ℕ}
        {rt1 rt2 : RelType R n}
        : (expression1 : ExpressionTerm rt1) →
          (expression2 : ExpressionTerm rt2) →
          FormulaTerm

      | bind
        {arity : Nat}
        {rel_type : ThoR.RelType R arity}
        {parameter_count : Nat}
        (quantor_type : Shared.quant)
        (disj : Bool)
        (parameter_names : Vector String parameter_count)
        : (pred : PredBind (R := R) ) →
          FormulaTerm

  inductive PredBind
    {R : Type}
    [ThoR.TupleSet R]
    where
      | pred
        {arity : Nat}
        {rel_type : ThoR.RelType R arity}
        {parameter_count : Nat}
        :
        (function :
          (Vector (ThoR.Rel rel_type) parameter_count) →
          FormulaTerm (R := R)
        ) →
        PredBind
  end


  inductive Term
    {R : Type}
    [ThoR.TupleSet R]
    where

      | expr : ExpressionTerm (R := R) t → Term
      | formula : FormulaTerm (R:= R)  → Term

      /--bracket definition-/
      | bracket : Term → Term

      | pred_def (name : String) : Term → Term

      /--function definition-/
      | fun_def (name : String) : Term → Term

      /- TODO: CHeck if lam and app are correct -/
      /- function abstraction -/
      | lam (t : RelType R n)
        : (Rel t → Term) → Term

      /- function application -/
      | app
        : Term →
          Term →
          Term

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

  def PredBind.ga
      {R : Type}
      [ThoR.TupleSet R]
      (t : @PredBind R _)
      : Nat :=
      match t with
        | @PredBind.pred R _ arity _ _ _ =>
          arity

    def PredBind.grt
      {R : Type}
      [ThoR.TupleSet R]
      (t : @PredBind R _)
      : RelType R (PredBind.ga t) :=
      match t with
        | @PredBind.pred R _ _ rel_type _ _ =>
          rel_type

mutual
  def ExpressionTerm.eval
    {R : Type}
    [ThoR.TupleSet R]
    {rt : RelType R n}
    (t : @ExpressionTerm R _ n rt)
    : ThoR.Rel rt :=
      match t with
      | .bracket t => t.eval

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
      (t : @FormulaTerm R _)
      : Prop :=
      match t with
        | .bracket t => t.eval

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

        | @FormulaTerm.bind
            R _ _ rt parameter_count quantor_type _ _ function =>
            let new_function :=
              (fun (pv : Vector (Rel rt) parameter_count) =>
                (function.eval) pv)

            let result := quantify_predicate new_function quantor_type

          result

    def PredBind.eval
      {R : Type}
      [ThoR.TupleSet R]
      (t : @PredBind R _)
      : Vector (Rel t.grt) parameter_count → Prop :=
      match t with
        | @PredBind.pred R _ arity rel_type parameter_count function =>
          fun (x : Vector (Rel rel_type) parameter_count ) =>
            (function x).eval

    def AlgebraTerm.eval
      {R : Type}
      [ThoR.TupleSet R]
      (t : @AlgebraTerm R _)
      : ℤ :=
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
    (t : @Term R _)
    : Prop :=
    match t with
    | .bracket t => t.eval

    | .expr t => t.eval

    | .formula t => t.eval

    | .pred_def _ t => t.eval

    | .fun_def _ t => t.eval

    /- TODO: Check if lam and app correct -/
    | @Term.lam R _ _ t f => λ (x : Rel t) => (f x).eval
    | .app f r => f.eval r.eval

  /- Coersions -/
  /- general eval -/
  instance
    {R : Type} [TupleSet R]
    {tyty : TyTy}
    {ty : @Ty R _ tyty}
    (t : @Term R _ tyty ty)
    :
    CoeDep _ t ty.eval where
      coe := t.eval

  /- Expression to Term -/
  instance
    {R : Type} [TupleSet R]
    (tyty : TyTy)
    (ty : Ty tyty (R := R))
    (t : @ExpressionTerm R _ tyty ty)
    :
    CoeDep
      _
      t
      (@Term R _ tyty ty)
    where
      coe := Term.expr t

  /- Formular to Term -/
  instance
    {R : Type} [TupleSet R]
    (tyty : TyTy)
    (ty : Ty tyty (R := R))
    (t : @FormulaTerm R _ tyty ty)
    :
    CoeDep
      _
      t
      (@Term R _ tyty ty)
    where
      coe := Term.formula t

  /- Formular to Term -/
  instance
    {R : Type} [TupleSet R]
    (tyty : TyTy)
    (ty : Ty tyty (R := R))
    (t : @FormulaTerm R _ tyty ty)
    :
    CoeDep
      _
      t
      (@Term R _ tyty ty)
    where
      coe := Term.formula t

  /- Term to Type -/
  instance
    {R : Type} [TupleSet R]
    {n : Nat}
    {rel_type : RelType R n}
    (t : @Term R _ (TyTy.isTy) (Ty.expression rel_type))
    :
    CoeDep
      _
      t
      Type
    where
      coe := Rel (RelType.mk.rel (t.eval))

  /- Expression to Type -/
  instance
    {R : Type} [TupleSet R]
    {n : Nat}
    {rel_type : RelType R n}
    (t : @ExpressionTerm R _ (TyTy.isTy) (Ty.expression rel_type))
    :
    CoeDep
      _
      t
      Type
    where
      coe := Term.expr t

  instance
    {R : Type} [TupleSet R]
    (t : @Term R _ (TyTy.isTy) (Ty.formula))
    :
    CoeDep
      _
      t
      Prop
    where
      coe := t.eval

end ThoR.Semantics
