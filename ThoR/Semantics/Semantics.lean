/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.quant
import ThoR.Relation.Quantification
import ThoR.Relation.Rel
-- import ThoR.Relation.Elab

import ThoR.Semantics.RelList

namespace ThoR.Semantics

variable (R : Type) [TupleSet R]

-- TODO: self-explaining variable names
-- TODO: possibly add an option to give arguments as an Array or List
--       -> heterogeneous lists
  inductive SemType {R : Type} [TupleSet R] : Type u where
    | number -- ℤ
    | formula -- Prop
    | expression : {n : ℕ} → (rel_type : RelType R n) → SemType -- Rel rel_type
    | expression_list : (indices : List (RelTypeWithArity R)) → SemType -- RelList indices
    | function : SemType → SemType → SemType -- st1.eval → st2.eval

  inductive Term {R : Type} [TupleSet R] : @SemType R _ → Type u where
    | rel {n : ℕ} {t : RelType R n} (r : Rel t) : Term (.expression t)
    | intersect {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Term (.expression (t1 & t2))
    -- | union {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 + t2)
    -- | diff {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 - t2)
    -- | cartprod {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ⟶ t2)
    -- | dotjoin {n1 n2 : ℕ} {t1 : RelType R (n1+1)} {t2 : RelType R (n2+2)} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ⋈ t2)
    | transclos {t : RelType R 2} (r : Rel t) : Term (.expression (^ t))
    -- | reftransclos {t : RelType R 2} (r : Rel t) : Expression (* t)
    -- | transpose {t : RelType R 2} (r : Rel t) : Expression (~ t)
    -- | append {n : ℕ} {t1 t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 ++ t2)
    -- | domrestr {n : ℕ} {t1 : RelType R 1} {t2 : RelType R n} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 <: t2)
    -- | rangerestr {n : ℕ} {t1 : RelType R n} {t2 : RelType R 1} (r1 : Rel t1) (r2 : Rel t2) : Expression (t1 :> t2)
    | if_then_else {n : ℕ} {t1 t2 : RelType R n} (f : Formula) (r1 : Rel t1) (r2 : Rel t2) : Term (.expression (RelType.ifThenElse t1 t2))
    --  Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
    -- | pred_abstraction {n : ℕ} {t : RelType R n} : Term (.expression t) → Term .formula → Term (.function (.expression t) .formula)

    | pred_abstraction {indices : List (RelTypeWithArity R)} : (RelList R indices → Term .formula) → Term (.function (.expression_list indices) .formula)

    | pred_application {indices : List (RelTypeWithArity R)} : Term (.function (.expression_list indices) .formula) → RelList R indices → Term .formula
    -- | call {n1 n2 : ℕ} {parameter_type : RelType R n1} {return_type : RelType R n2} (f : Function parameter_type return_type) (parameter : Expression parameter_type) : Expression return_type
    -- | let {n1 n2 : ℕ} {parameter_type : RelType R n1} {return_type : RelType R n2} (l : ExpressionLet parameter_type return_type) (e : Expression parameter_type) : Expression return_type

  -- inductive Function : {n1 n2: ℕ} → RelType R n1 → RelType R n2 → Type u where
  --   | mk {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (f : (Rel t1) → Expression t2): Function t1 t2

  -- inductive ExpressionLet : {n1 n2: ℕ} → RelType R n1 → RelType R n2 → Type u where
  --   | mk {n1 n2 : ℕ} {t1 : RelType R n1} {t2 : RelType R n2} (f : (Rel t1) → Expression t2): ExpressionLet t1 t2

  -- inductive ArithmeticExpression : Type u where
    | number (z : ℤ) : Term .number
    | negation : Term .number → Term .number
    | add : Term .number → Term .number → Term .number
    -- | sub (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    -- | mult (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    -- | div (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    -- | rem (a1 a2 : ArithmeticExpression) : ArithmeticExpression
    | card {n : ℕ} {t : RelType R n} : Term (.expression t) → Term .number

  -- inductive Formula : Type u where
    | no {n : ℕ} {t : RelType R n} : Term (.expression t) → Term .formula
    -- | lone {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    -- | one {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    -- | some {n : ℕ} {t : RelType R n} (e : Expression t) : Formula
    | not : Term .formula → Term .formula
    | or : Term .formula → Term .formula → Term .formula
    -- | and (f1 f2 : Formula) : Formula
    -- | equivalent (f1 f2 : Formula) : Formula
    -- | implication (f1 f2 : Formula) : Formula
    | f_if_then_else : Term .formula → Term .formula → Term .formula → Term .formula
    | a_lt : Term .number → Term .number → Term .formula
    -- | a_gt (a1 a2 : ArithmeticExpression) : Formula
    -- | a_eq (a1 a2 : ArithmeticExpression) : Formula
    -- | a_leq (a1 a2 : ArithmeticExpression) : Formula
    -- | a_geq (a1 a2 : ArithmeticExpression) : Formula
    | in {n : ℕ} {t1 t2 : RelType R n} : Term (.expression t1) → Term (.expression t2) → Term .formula
    -- | eq {n : ℕ} {t1 t2 : RelType R n} (e1 : Expression t1) (e2 : Expression t2) : Formula
    -- | neq {n : ℕ} {t1 t2 : RelType R n} (e1 : Expression t1) (e2 : Expression t2) : Formula
    | q_no {n : ℕ} {t : RelType R n} : Term (.function (.expression t) ran) → Term .formula -- (f : (Rel t) → Formula): Formula
  --   | q_lone {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
  --   | q_one {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
  --   | q_some {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
  --   | q_all {n : ℕ} {t : RelType R n} (f : (Rel t) → Formula): Formula
  --   | call {n : ℕ} {t : RelType R n} (p : Predicate t) (e : Expression t) : Formula
  --   | let {n : ℕ} {t : RelType R n} (l : FormulaLet t) (e : Expression t) : Formula

  -- inductive Predicate : {n: ℕ} → RelType R n → Type u where
  --   | mk {n : ℕ} {t : RelType R n} (p : (Rel t) → Formula): Predicate t

  -- inductive FormulaLet : {n: ℕ} → RelType R n → Type u where
  --   | mk {n : ℕ} {t : RelType R n} (p : (Rel t) → Formula): FormulaLet t

-- mutual
--   def Expression.eval {n : ℕ } {t : RelType R n} (e : @Expression R _ _ t) :=
--     match e with
--     | .rel              r       => r
--     | .intersect        r1 r2   => r1 & r2
--     | .union            r1 r2   => r1 + r2
--     | .diff             r1 r2   => r1 -r2
--     | .cartprod         r1 r2   => r1 ⟶ r2
--     | .dotjoin          r1 r2   => r1 ⋈ r2
--     | .transclos        r       => ^ r
--     | .reftransclos     r       => * r
--     | .transpose        r       => ~ r
--     | .append           r1 r2   => r1 ++ r2
--     | .domrestr         r1 r2   => r1 <: r2
--     | .rangerestr       r1 r2   => r1 :> r2
--     | .if_then_else     f r1 r2 => HIfThenElse.hIfThenElse f.eval r1 r2
--     | @Expression.call  _ _ _ _ t1 t2 f e     => (f.eval : Rel t1 → Rel t2) e.eval
--     | @Expression.let   _ _ _ _ t1 t2 l e     => (l.eval : Rel t1 → Rel t2) e.eval

--   def Function.eval {n1 n2 : ℕ } {t1 : RelType R n1} {t2 : RelType R n2} (f : @Function R _ _ _ t1 t2) :=
--       match f with
--       | .mk f => (fun (r : Rel t1) => (f r).eval : Rel t1 → Rel t2)

--   def ExpressionLet.eval {n1 n2 : ℕ } {t1 : RelType R n1} {t2 : RelType R n2} (l : @ExpressionLet R _ _ _ t1 t2) :=
--       match l with
--       | .mk f => (fun (r : Rel t1) => (f r).eval : Rel t1 → Rel t2)

--   def ArithmeticExpression.eval (a : @ArithmeticExpression R _) :=
--     match a with
--     | .number   z     => z
--     | .negation a     => - a.eval
--     | .add      a1 a2 => a1.eval + a2.eval
--     | .sub      a1 a2 => a1.eval - a2.eval
--     | .mult     a1 a2 => a1.eval * a2.eval
--     | .div      a1 a2 => a1.eval / a2.eval
--     | .rem      a1 a2 => a1.eval % a2.eval
--     | .card     r     => Card.card r

--   def Formula.eval (f : @Formula R _) :=
--     match f with
--     | .no           e         => SetMultPredicates.no e.eval
--     | .lone         e         => SetMultPredicates.lone e.eval
--     | .one          e         => SetMultPredicates.one e.eval
--     | .some         e         => SetMultPredicates.some e.eval
--     | .not          f         => ¬ f.eval
--     | .or           f1 f2     => f1.eval ∨ f2.eval
--     | .and          f1 f2     => f1.eval ∧ f2.eval
--     | .equivalent   f1 f2     => f1.eval ↔ f2.eval
--     | .implication  f1 f2     => f1.eval → f2.eval
--     | .if_then_else f f1 f2   => (f.eval → f1.eval) ∧ (¬ f.eval → f2.eval)
--     | .a_lt         a1 a2     => a1.eval < a2.eval
--     | .a_gt         a1 a2     => a1.eval > a2.eval
--     | .a_eq         a1 a2     => a1.eval = a2.eval
--     | .a_leq        a1 a2     => a1.eval ≤ a2.eval
--     | .a_geq        a1 a2     => a1.eval ≥ a2.eval
--     | .in           r1 r2     => r1.eval ⊂ r2.eval
--     | .eq           r1 r2     => r1.eval ≡ r2.eval
--     | .neq          r1 r2     => ¬ (r1.eval ≡ r2.eval)
--     | .q_no         f         => (Quantification.Formula.var Shared.quant.no (fun r => (Quantification.Formula.prop (f r).eval))).eval
--     | .q_lone       f         => (Quantification.Formula.var Shared.quant.lone (fun r => (Quantification.Formula.prop (f r).eval))).eval
--     | .q_one        f         => (Quantification.Formula.var Shared.quant.one (fun r => (Quantification.Formula.prop (f r).eval))).eval
--     | .q_some       f         => (Quantification.Formula.var Shared.quant.some (fun r => (Quantification.Formula.prop (f r).eval))).eval
--     | .q_all        f         => (Quantification.Formula.var Shared.quant.all (fun r => (Quantification.Formula.prop (f r).eval))).eval
--     | @Formula.call _ _ _ t p e    => (p.eval : Rel t → Prop) e.eval
--     | @Formula.let  _ _ _ t l e    => (l.eval : Rel t → Prop) e.eval

--   def Predicate.eval {n : ℕ } {t : RelType R n} (p : @Predicate R _ _ t) :=
--     match p with
--     | .mk pred => (fun (r : Rel t) => (pred r).eval : Rel t → Prop)

--   def FormulaLet.eval {n : ℕ } {t : RelType R n} (p : @FormulaLet R _ _ t) :=
--     match p with
--     | .mk pred => (fun (r : Rel t) => (pred r).eval : Rel t → Prop)

--   def SemType.eval {n : ℕ} (te : @SemType R _ n) :=
--     match te with
--     | .rel_type t => t
-- end

-- end ThoR.Semantics

-- open ThoR
-- -- TODO Coercions for
-- -- [ ] ExpressionLet
-- -- [ ] ArithmeticExpression
-- -- [ ] Predicate
-- -- [ ] FormulaLet
-- -- [ ] SemType

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


def u := Term.rel (@vars.UNIV ThoR_TupleSet _ _)
#check u

#check Term.in (@u ThoR_TupleSet _ _) (@u ThoR_TupleSet _ _)
def pred1 :=
  Term.pred_abstraction (
    λ (r1 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
      Term.pred_abstraction'' (
        λ (r2 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
          Term.pred_abstraction' (
            λ (r3 : Rel (RelType.mk.sig ThoR_TupleSet Shared.mult.set)) =>
              Term.or (Term.in (Term.rel r1) (Term.rel r2)) (Term.in (Term.rel r2) (Term.rel r3))
          )
      )
  )


#check @pred1 ThoR_TupleSet _
#check Term.pred_application (@pred1 ThoR_TupleSet _ ) (@u ThoR_TupleSet _  _)
