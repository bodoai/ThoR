/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.quant
import ThoR.Relation.Quantification
import ThoR.Relation.Rel

namespace ThoR.Semantics

#check RelType
#check Rel

inductive RelTypeList (R : Type u) [TupleSet R] : List ℕ → Type u
  | nil : RelTypeList R []
  | cons : {n : ℕ} → (RelType R n) → (ns : List ℕ) → (RelTypeList R ns) → RelTypeList R (n::ns)

inductive RelList (R : Type u) [TupleSet R] : {arities : List ℕ} → RelTypeList R arities→ Type u
  | nil : RelList R RelTypeList.nil
  | cons : {n : ℕ} → {type : RelType R n} → (r : ThoR.Rel type) → {arities : List ℕ} → (types : RelTypeList arities) → (rs : RelList R types) → RelList R (type::types)

#print List


variable {R : Type} [TupleSet R]

-- #check R
-- #check @RList.nil R

-- variable (t1 : RelType R 1) (t2 : RelType R 7)
-- def l1 := RList.cons t1 RList.nil



-- inductive MyList (α : Type) :=
--   | nil : MyList α
--   | cons : α → MyList α → MyList α

-- inductive MyHList {α : Type v}: List (Type α) → Type v
--   | nil : MyHList []
--   | cons (h_type : Type u) (h : h_type) (t_type : List (Type (max u v))) (MyHList t_type) : MyHList (h_type :: t_type)


-- TODO: self-explaining variable names
-- TODO: possibly add an option to give arguments as an Array or List
--       -> heterogeneous lists
mutual
  inductive Expression : {n: ℕ} → RelType R n → Type u where
    | rel {n : ℕ} {t : RelType R n} (r : Rel t) : Expression t
    | intersect {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 & t2)
    | union {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 + t2)
    | diff {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 - t2)
    | cartprod {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ⟶ t2)
    | dotjoin {n1 n2 : ℕ} {t1 : RelType R (n1+1)} {t2 : RelType R (n2+2)} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ⋈ t2)
    | transclos {t : RelType R 2} (r : Rel t) : Expression (^ t)
    | reftransclos {t : RelType R 2} (r : Rel t) : Expression (* t)
    | transpose {t : RelType R 2} (r : Rel t) : Expression (~ t)
    | append {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ++ t2)
    | domrestr {n : ℕ} {t1 : RelType R 1} {t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 <: t2)
    | rangerestr {n : ℕ} {t1 : RelType R n} {t2 : RelType R 1} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 :> t2)
    | if_then_else {n : ℕ} {t1 t2 : RelType R n} (f : Formula) (r1 : Rel t1) (r2 : Rel t2) : Expression (RelType.ifThenElse t1 t2)
    | call {n1 n2 : ℕ} {parameter_type : RelType R n1} {return_type : RelType R n2} (f : Function parameter_type return_type) (parameter : Expression parameter_type) : Expression return_type
    | let {n1 n2 : ℕ} {parameter_type : RelType R n1} {return_type : RelType R n2} (l : ExpressionLet parameter_type return_type) (e : Expression parameter_type) : Expression return_type

  inductive Function : {arg_arities : List ℕ} → {res_arity: ℕ} → RList R arg_arities → RelType R res_arity → Type u where
    | mk {arg_arities : List ℕ} {res_arity: ℕ}  {res_type : RelType R res_arity} (f : RList R arg_arities → Expression res_type): Function t1 t2

  inductive ExpressionLet : {n1 n2: ℕ} → RelType R n1 → RelType R n2 → Type u where
    | mk {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (f : (Rel t1) → Expression t2): ExpressionLet t1 t2

  inductive ArithmeticExpression : Type u where
    | number (z : ℤ) : ArithmeticExpression
    | negation (a : ArithmeticExpression) : ArithmeticExpression
    | add (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | sub (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | mult (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | div (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | rem (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | card {n : ℕ} {t : RelType R n} (r : Rel t) : ArithmeticExpression

  inductive Formula : Type u where
    | no {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    | lone {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    | one {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    | some {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    | not (f : Formula) : Formula
    | or (f1 f2 : Formula) : Formula
    | and (f1 f2 : Formula) : Formula
    | equivalent (f1 f2 : Formula) : Formula
    | implication (f1 f2 : Formula) : Formula
    | if_then_else (f1 f2 f3 : Formula) : Formula
    | a_lt (a1 a2 : ArithmeticExpression) : Formula
    | a_gt (a1 a2 : ArithmeticExpression) : Formula
    | a_eq (a1 a2 : ArithmeticExpression) : Formula
    | a_leq (a1 a2 : ArithmeticExpression) : Formula
    | a_geq (a1 a2 : ArithmeticExpression) : Formula
    | in {n : ℕ} {t1 t2 : RelType R n} (e1 : Expression t1) (e2 : Expression t2): Formula
    | eq {n : ℕ} {t1 t2 : RelType R n} (e1 : Expression t1) (e2 : Expression t2) : Formula
    | neq {n : ℕ} {t1 t2 : RelType R n} (e1 : Expression t1) (e2 : Expression t2) : Formula
    | q_no {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
    | q_lone {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
    | q_one {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
    | q_some {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
    | q_all {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
    | call {n : ℕ} {t : RelType R n} (p : Predicate t) (e : Expression t) : Formula
    | let {n : ℕ} {t : RelType R n} (l : FormulaLet t) (e : Expression t) : Formula

  inductive Predicate : {n: ℕ} → RelType R n → Type u where
    | mk {n : ℕ} {t : RelType R n} (p : (Rel t) → Formula): Predicate t

  inductive FormulaLet : {n: ℕ} → RelType R n → Type u where
    | mk {n : ℕ} {t : RelType R n} (p : (Rel t) → Formula): FormulaLet t

  inductive TypeExpression : ℕ → Type u where
    | type {n : ℕ} (t : RelType R n) : TypeExpression n
end

mutual
  def Expression.eval {n : ℕ } {t : RelType R n} (e : @Expression R _ _ t) :=
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
    | @Expression.call  _ _ _ _ t1 t2 f e     => (f.eval : Rel t1 → Rel t2) e.eval
    | @Expression.let   _ _ _ _ t1 t2 l e     => (l.eval : Rel t1 → Rel t2) e.eval

  def Function.eval {n1 n2 : ℕ } {t1 : RelType R n1} {t2 : RelType R n2} (f : @Function R _ _ _ t1 t2) :=
      match f with
      | .mk f => (fun (r : Rel t1) => (f r).eval : Rel t1 → Rel t2)

  def ExpressionLet.eval {n1 n2 : ℕ } {t1 : RelType R n1} {t2 : RelType R n2} (l : @ExpressionLet R _ _ _ t1 t2) :=
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

  def Formula.eval (f : @Formula R _) :=
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
    | @Formula.call _ _ _ t p e    => (p.eval : Rel t → Prop) e.eval
    | @Formula.let  _ _ _ t l e    => (l.eval : Rel t → Prop) e.eval

  def Predicate.eval {n : ℕ } {t : RelType R n} (p : @Predicate R _ _ t) :=
    match p with
    | .mk pred => (fun (r : Rel t) => (pred r).eval : Rel t → Prop)

  def FormulaLet.eval {n : ℕ } {t : RelType R n} (p : @FormulaLet R _ _ t) :=
    match p with
    | .mk pred => (fun (r : Rel t) => (pred r).eval : Rel t → Prop)

  def TypeExpression.eval {n : ℕ} (te : @TypeExpression R _ n) :=
    match te with
    | .type t => t
end

end ThoR.Semantics
