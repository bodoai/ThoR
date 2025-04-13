/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Rel

-- FIXME: Präzedenzen der Operatoren mit Lean.Notation abgleichen

namespace ThoR.Semantics

variable {R : Type} [TupleSet R]

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
    -- | if_then_else {n : ℕ} {t1 t2 : RelType R n} (f : Formula) (r1 : Rel t1) (r2 : Rel t2) : Expression ?
-- function
-- let

  inductive TypeExpression : ℕ → Type u where
    | unary_rel {t : RelType R 1} (m : Shared.mult) (r : Rel t) : TypeExpression n
    | rel {n : ℕ} {t : RelType R n} (r : Rel t) : TypeExpression n
    | complex {n1 n2 : ℕ} (te1 : TypeExpression n1) (te2: TypeExpression n2) : TypeExpression (n1 + n2)

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
end

mutual
  def Expression.eval {n : ℕ } {t : RelType R n} (e : Expression t) :=
    match e with
    | rel           r       => r
    | intersect     r1 r2   => r1 & r2
    | union         r1 r2   => r1 + r2
    | diff          r1 r2   => r1 -r2
    | cartprod      r1 r2   => r1 ⟶ r2
    | dotjoin       r1 r2   => r1 ⋈ r2
    | transclos     r       => ^ r
    | reftransclos  r       => * r
    | transpose     r       => ~ r
    | append        r1 r2   => r1 ++ r2
    | domrestr      r1 r2   => r1 <: r2
    | rangerestr    r1 r2   => r1 :> r2
end

end ThoR.Semantics
