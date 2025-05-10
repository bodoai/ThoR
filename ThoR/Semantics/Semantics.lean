/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.quant
import ThoR.Relation.Quantification
import ThoR.Relation.Rel

namespace ThoR

-- definition from https://lean-lang.org/documentation/examples/debruijn/
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons
notation "[" "]" => HList.nil

def HList.map.{u, v} {α : Type v} {β₁ : α → Type u} {β₂ : α → Type u} (f : {i: α} → (β₁ i) → (β₂ i)) {indices :List α} (l : HList β₁ indices) : HList β₂ indices
:=
    match l with
    | [] => []
    | h :: t => (f h) :: (HList.map f t)

#print List.foldl
--  	(a -> b -> a) -> a -> [b] -> a

def HList.foldl.{u, v} {α : Type v} {β : α → Type u} {γ : Type} {indices :List α} (l : HList β indices) (f : {i: α} → γ → (β i) → γ) (acc : γ) : γ
:=
    match l with
    | [] => acc
    | h :: t => f (HList.foldl t f acc) h


-- abbrev RelTypeWithArity (R : Type) [TupleSet R] := Sigma (RelType R)
abbrev RelTypeWithDepth (R : Type) [TupleSet R] := (Sigma (RelType R)) × ℕ

abbrev RelList (R : Type) [TupleSet R] := HList (λ (type : RelTypeWithArity R) => Rel type.2)

end ThoR

namespace ThoR.Semantics

variable {R : Type} [TupleSet R]

-- TODO: self-explaining variable names
-- TODO: possibly add an option to give arguments as an Array or List
--       -> heterogeneous lists
mutual
  inductive Expression : {arity: ℕ} → RelType R arity → (depth : ℕ) → Type u where
    | rel {arity : ℕ} {t : RelType R arity} (r : Rel t) : Expression t 0
    | intersect {arity : ℕ} {t1 t2 : RelType R arity} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 & t2) 0
    | union {arity : ℕ} {t1 t2 : RelType R arity} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 + t2) 0
    | diff {arity : ℕ} {t1 t2 : RelType R arity} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 - t2) 0
    | cartprod {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ⟶ t2) 0
    | dotjoin {n1 n2 : ℕ} {t1 : RelType R (n1+1)} {t2 : RelType R (n2+2)} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ⋈ t2) 0
    | transclos {t : RelType R 2} (r : Rel t) : Expression (^ t) 0
    | reftransclos {t : RelType R 2} (r : Rel t) : Expression (* t) 0
    | transpose {t : RelType R 2} (r : Rel t) : Expression (~ t) 0
    | append {arity : ℕ} {t1 t2 : RelType R arity} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ++ t2) 0
    | domrestr {arity : ℕ} {t1 : RelType R 1} {t2 : RelType R arity} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 <: t2) 0
    | rangerestr {arity : ℕ} {t1 : RelType R arity} {t2 : RelType R 1} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 :> t2) 0
    | if_then_else {arity : ℕ} {t1 t2 : RelType R arity} (f : Formula depth) (r1 : Rel t1) (r2 : Rel t2) : Expression (RelType.ifThenElse t1 t2) 1
    | call {n1 n2 : ℕ} {parameter_type : RelType R n1} {return_type : RelType R n2} (f : Function parameter_type return_type parameter_type_depth) (parameter : Expression parameter_type parameter_depth) : Expression return_type ((max parameter_type_depth parameter_depth) + 1)
    | let {n1 n2 : ℕ} {parameter_type : RelType R n1} {return_type : RelType R n2} (l : ExpressionLet parameter_type return_type parameter_type_depth) (e : Expression parameter_type expression_depth) : Expression return_type ((max parameter_type_depth expression_depth) + 1)

  inductive Function : {n1 n2: ℕ} → RelType R n1 → RelType R n2 → (depth : ℕ) → Type u where
    | mk {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (f : (Rel t1) → Expression t2 depth): Function t1 t2 (depth + 1)

  inductive ExpressionLet : {n1 n2: ℕ} → RelType R n1 → RelType R n2 → (depth : ℕ) → Type u where
    | mk {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (f : (Rel t1) → Expression t2 depth): ExpressionLet t1 t2 (depth + 1)

  inductive ArithmeticExpression : Type u where
    | number (z : ℤ) : ArithmeticExpression
    | negation (a : ArithmeticExpression) : ArithmeticExpression
    | add (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | sub (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | mult (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | div (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | rem (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | card {arity : ℕ} {t : RelType R arity} (r : Rel t) : ArithmeticExpression

  inductive Formula : (depth : ℕ) → Type u where
    | no {arity : ℕ} {t : RelType R arity} (e : Expression t depth) : Formula (depth + 1)
    | lone {arity : ℕ} {t : RelType R arity} (e : Expression t depth) : Formula (depth + 1)
    | one {arity : ℕ} {t : RelType R arity} (e : Expression t depth) : Formula (depth + 1)
    | some {arity : ℕ} {t : RelType R arity} (e : Expression t depth) : Formula (depth + 1)
    | not (f : Formula depth) : Formula (depth + 1)
    | or (f1 : Formula depth1) (f2 : Formula depth2) : Formula ((max depth1 depth2) + 1)
    | and (f1 : Formula depth1) (f2 : Formula depth2) : Formula ((max depth1 depth2) + 1)
    | equivalent (f1 : Formula depth1) (f2 : Formula depth2) : Formula ((max depth1 depth2) + 1)
    | implication (f1 : Formula depth1) (f2 : Formula depth2) : Formula ((max depth1 depth2) + 1)
    | if_then_else (f1 : Formula depth1) (f2 : Formula depth2) (f3 : Formula depth3): Formula ((max (max depth1 depth2) depth3) + 1)
    | a_lt (a1 a2 : ArithmeticExpression) : Formula 0
    | a_gt (a1 a2 : ArithmeticExpression) : Formula 0
    | a_eq (a1 a2 : ArithmeticExpression) : Formula 0
    | a_leq (a1 a2 : ArithmeticExpression) : Formula 0
    | a_geq (a1 a2 : ArithmeticExpression) : Formula 0
    | in {arity : ℕ} {t1 t2 : RelType R arity} (e1 : Expression t1 depth1) (e2 : Expression t2 depth2): Formula ((max depth1 depth2) + 1)
    | eq {arity : ℕ} {t1 t2 : RelType R arity} (e1 : Expression t1 depth1) (e2 : Expression t2 depth2): Formula ((max depth1 depth2) + 1)
    | neq {arity : ℕ} {t1 t2 : RelType R arity} (e1 : Expression t1 depth1) (e2 : Expression t2 depth2): Formula ((max depth1 depth2) + 1)
    | q_no {arity : ℕ} {t : RelType R arity} (f : (Rel t) → Formula depth): Formula (depth + 1)
    | q_lone {arity : ℕ} {t : RelType R arity} (f : (Rel t) → Formula depth): Formula (depth + 1)
    | q_one {arity : ℕ} {t : RelType R arity} (f : (Rel t) → Formula depth): Formula (depth + 1)
    | q_some {arity : ℕ} {t : RelType R arity} (f : (Rel t) → Formula depth): Formula (depth + 1)
    | q_all {arity : ℕ} {t : RelType R arity} (f : (Rel t) → Formula depth): Formula (depth + 1)
    | call {rel_types_w_depth : List ((RelTypeWithArity R) × ℕ)} (p : Predicate rel_types pred_depth) (params : ThoR.HList (λ (type_w_depth : (RelTypeWithArity R) × ℕ) => Expression type_w_depth.1.2 type_w_depth.2) rel_types_w_depth) :
      Formula ((max (rel_types_w_depth.foldl (λ depth param => max depth param.2) 0 ) depth) + 1)
    | let {arity : ℕ} {t : RelType R arity} (l : FormulaLet t l_depth) (e : Expression t e_depth) : Formula ((max l_depth e_depth) + 1)


  inductive Predicate : List (RelTypeWithArity R) → (depth : ℕ) → Type u where
    | mk (rel_types : List (RelTypeWithArity R)) (predicate : (RelList R rel_types) → Formula depth): Predicate rel_types (depth + 1)

  inductive FormulaLet : {arity: ℕ} → RelType R arity → (depth : ℕ) → Type u where
    | mk {arity : ℕ} {t : RelType R arity} (p : (Rel t) → Formula depth): FormulaLet t (depth + 1)

  inductive TypeExpression : ℕ → Type u where
    | type {arity : ℕ} (t : RelType R arity) : TypeExpression arity
end

mutual
  def Expression.eval {arity : ℕ } {t : RelType R arity} (e : @Expression R _ _ t d) : (Rel t) :=
    match e with
    | .rel              r       => r
    | .intersect        r1 r2   => r1 & r2
    | .union            r1 r2   => r1 + r2
    | .diff             r1 r2   => r1 -r2
    | .cartprod         r1 r2   => r1 ⟶ r2
    | .dotjoin          r1 r2   => r1 ⋈ r2
    | .transclos        r       => ^ r
    | .reftransclos     r       => * r
    | .transpose        r       => ~ r
    | .append           r1 r2   => r1 ++ r2
    | .domrestr         r1 r2   => r1 <: r2
    | .rangerestr       r1 r2   => r1 :> r2
    | .if_then_else     f r1 r2 => HIfThenElse.hIfThenElse f.eval r1 r2
    | @Expression.call  _ _ _ _ _ _ t1 t2 f e     => (f.eval : Rel t1 → Rel t2) e.eval
    | @Expression.let   _ _ _ _ _ _ t1 t2 l e     => (l.eval : Rel t1 → Rel t2) e.eval

  def Function.eval {n1 n2 : ℕ } {t1 : RelType R n1} {t2 : RelType R n2} (f : @Function R _ _ _ t1 t2 d) :=
      match f with
      | .mk f => (fun (r : Rel t1) => (f r).eval : Rel t1 → Rel t2)

  def ExpressionLet.eval {n1 n2 : ℕ } {t1 : RelType R n1} {t2 : RelType R n2} (l : @ExpressionLet R _ _ _ t1 t2 d) :=
      match l with
      | .mk f => (fun (r : Rel t1) => (f r).eval : Rel t1 → Rel t2)

  def ArithmeticExpression.eval (a : @ArithmeticExpression R _) :=
    match a with
    | .number   z     => z
    | .negation a     => - a.eval
    | .add      a1 a2 => a1.eval + a2.eval
    | .sub      a1 a2 => a1.eval - a2.eval
    | .mult     a1 a2 => a1.eval * a2.eval
    | .div      a1 a2 => a1.eval / a2.eval
    | .rem      a1 a2 => a1.eval % a2.eval
    | .card     r     => Card.card r

  def Formula.eval (f : @Formula R _ d) :=
    match f with
    | .no           e         => SetMultPredicates.no e.eval
    | .lone         e         => SetMultPredicates.lone e.eval
    | .one          e         => SetMultPredicates.one e.eval
    | .some         e         => SetMultPredicates.some e.eval
    | .not          f         => ¬ f.eval
    | .or           f1 f2     => f1.eval ∨ f2.eval
    | .and          f1 f2     => f1.eval ∧ f2.eval
    | .equivalent   f1 f2     => f1.eval ↔ f2.eval
    | .implication  f1 f2     => f1.eval → f2.eval
    | .if_then_else f f1 f2   => (f.eval → f1.eval) ∧ (¬ f.eval → f2.eval)
    | .a_lt         a1 a2     => a1.eval < a2.eval
    | .a_gt         a1 a2     => a1.eval > a2.eval
    | .a_eq         a1 a2     => a1.eval = a2.eval
    | .a_leq        a1 a2     => a1.eval ≤ a2.eval
    | .a_geq        a1 a2     => a1.eval ≥ a2.eval
    | .in           r1 r2     => r1.eval ⊂ r2.eval
    | .eq           r1 r2     => r1.eval ≡ r2.eval
    | .neq          r1 r2     => ¬ (r1.eval ≡ r2.eval)
    | .q_no         f         => (Quantification.Formula.var Shared.quant.no (fun r => (Quantification.Formula.prop (f r).eval))).eval
    | .q_lone       f         => (Quantification.Formula.var Shared.quant.lone (fun r => (Quantification.Formula.prop (f r).eval))).eval
    | .q_one        f         => (Quantification.Formula.var Shared.quant.one (fun r => (Quantification.Formula.prop (f r).eval))).eval
    | .q_some       f         => (Quantification.Formula.var Shared.quant.some (fun r => (Quantification.Formula.prop (f r).eval))).eval
    | .q_all        f         => (Quantification.Formula.var Shared.quant.all (fun r => (Quantification.Formula.prop (f r).eval))).eval
    | @Formula.call _ _ _ _ _ rel_types_w_depth predicate params    =>
      -- let rel_types := rel_types_w_depth.map Prod.fst
      -- (predicate.eval : RelList R rel_types → Prop) (ExpressionList_eval params)
      predicate.eval (ExpressionList_eval params)
    | @Formula.let  _ _ _ _ _ t l e    => (l.eval : Rel t → Prop) e.eval

-- (params : ThoR.HList (λ (type_w_depth : (RelTypeWithArity R) × ℕ) => Expression type_w_depth.1.2 type_w_depth.2) rel_types_w_depth)

    def ExpressionList_eval {rel_types_w_depth : List ((RelTypeWithArity R) × ℕ)} (params : ThoR.HList (λ (type_w_depth : (RelTypeWithArity R) × ℕ) => Expression type_w_depth.1.2 type_w_depth.2) rel_types_w_depth)
    :=
      HList.map (λ {type_w_depth: (RelTypeWithArity R) × ℕ} (e : Expression type_w_depth.1.2 type_w_depth.2) => e.eval) params

  def Predicate.eval {rel_types : List (RelTypeWithArity R)} (p : Predicate rel_types depth) : RelList R rel_types → Prop :=
    match p with
    | .mk rel_types predicate =>
      ((fun (params : RelList R rel_types) => (predicate params).eval) : RelList R rel_types → Prop)

  def FormulaLet.eval {arity : ℕ } {t : RelType R arity} (p : @FormulaLet R _ _ t d) :=
    match p with
    | .mk pred => (fun (r : Rel t) => (pred r).eval : Rel t → Prop)

  def TypeExpression.eval {arity : ℕ} (te : @TypeExpression R _ arity) :=
    match te with
    | .type t => t
end

end ThoR.Semantics

open ThoR
-- TODO Coercions for
-- [ ] ExpressionLet
-- [ ] ArithmeticExpression
-- [ ] Predicate
-- [ ] FormulaLet
-- [ ] TypeExpression

-- -- Coercion Formula -> Prop
-- instance {R : Type} [ThoR.TupleSet R]:
--   CoeSort.{u+1} (@ThoR.Semantics.Formula.{u} R _) Prop where
--     coe f := ThoR.Semantics.Formula.eval.{u,u+1} f

-- -- Coercion Expression t -> Rel t
-- instance {R : Type} [ThoR.TupleSet R] {n : ℕ} {t : ThoR.RelType R n}:
--   CoeSort.{u+1} (@ThoR.Semantics.Expression.{u} R _ _ t) (ThoR.Rel t) where
--     coe e := ThoR.Semantics.Expression.eval.{u,u+1} e

-- -- Coercion Function
-- instance {R : Type} [ThoR.TupleSet R] {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2}:
--   CoeSort.{u+1} (ThoR.Semantics.Function.{u} t1 t2) (Rel t1 → Rel t2) where
--     coe e := ThoR.Semantics.Function.eval.{u,u+1} e
