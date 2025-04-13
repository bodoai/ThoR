/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Relation.Notation
import ThoR.Relation.TupleSetRules
import ThoR.Shared.Syntax.multType

-- FIXME: Präzedenzen der Operatoren mit Lean.Notation abgleichen
-- FIXME: eigene Datei für die Definition aller Operator-Typ-Klassen
namespace ThoR

-- TODO sub type relation: t1 ⊑ t2
--      true -> (∀ (r ∷ t1), (r ∷ t2)) → t1 ⊑ t2
--      test stub: true -> t1 = t2

inductive RelType' (R : Type) [TupleSet R] : Type :=
  | sig (m : Shared.mult) : RelType' R
  | unary_rel (m : Shared.mult) (r : R) : HasArity.hasArity r 1 -> RelType' R
  | rel (r : R) (n : ℕ): HasArity.hasArity r n → RelType' R
  | constant (c : R) (n : ℕ): HasArity.hasArity c n → RelType' R
  | complex
    (t1 : RelType' R) (m1 m2 : Shared.mult) (t2 : RelType' R) : RelType' R
  | intersect (t1 : RelType' R) (t2 : RelType' R) : RelType' R
  | add (t1 : RelType' R) (t2 : RelType' R): RelType' R
  | sub (t1 : RelType' R) (t2 : RelType' R):
      RelType' R
  | append (t1 : RelType' R) (t2 : RelType' R):
      RelType' R
  | cartprod (t1 : RelType' R) (t2 : RelType' R):
      RelType' R
  | dotjoin (t1 : RelType' R) (t2 : RelType' R) :  RelType' R
  | transclos (t : RelType' R):
      RelType' R
  | reftransclos (t : RelType' R):
      RelType' R
  | transpose (t : RelType' R):
      RelType' R
  | domrestr (t1 : RelType' R) (t2 : RelType' R):
      RelType' R
  | rangerestr (t1 : RelType' R) (t2 : RelType' R):
      RelType' R
  | if_then_else (t1 : RelType' R) (t2 : RelType' R) : RelType' R


-- Why define checkArityEq as a macro and not as a function?
-- Putting this into a macro makes it easier to implement RelType'.arity.
-- Putting this into a function requires an explicit proof for termination of arity.
local macro "checkArityEq" "(" arity:term ", " t1:term ", " t2:term ")": term =>
`(do
    let n1 ← ($arity $t1)
    let n2 ← ($arity $t2)
    if (n1 = n2)
    then return n1
    else none)

local macro "checkArityN" "(" arity:term ", " t:term ", " n:term ")": term =>
`(do
    let tn ← ($arity $t)
    if (tn = $n)
    then return $n
    else none)

@[simp]
def RelType'.arity {R : Type} [TupleSet R] (t : RelType' R) :=
  match t with
  | RelType'.sig _    => some 1
  | unary_rel _ _ _   => some 1
  | rel _ n _         => some n
  | constant _ n _    => some n
  | complex t1 _ _ t2 => Nat.add <*> t1.arity <*> t2.arity
  | intersect t1 t2   => checkArityEq (arity, t1, t2)
  | add t1 t2   => checkArityEq (arity, t1, t2)
  | sub t1 t2   => checkArityEq (arity, t1, t2)
  | append t1 t2   => checkArityEq (arity, t1, t2)
  | cartprod t1 t2 => Nat.add <*> t1.arity <*> t2.arity
  | dotjoin t1 t2 => do
                      let n1 ← t1.arity
                      let n2 ← t2.arity
                      if (n1 > 0 ∧ n2 >0)
                      then return n1 + n2 - 2
                      else none
  | transclos t => checkArityN (arity, t, 2)
  | reftransclos t => checkArityN (arity, t, 2)
  | transpose t => checkArityN (arity, t, 2)
  | domrestr t1 t2 => do
                        let _ ← checkArityN (arity, t1, 1)
                        let n2 ← t2.arity
                        return n2
  | rangerestr t1 t2 => do
                        let n1 ← t1.arity
                        let _ ← checkArityN (arity, t2, 1)
                        return n1
  | if_then_else t1 t2   => checkArityEq (arity, t1, t2)

def RelType (R : Type) [TupleSet R] (n : ℕ):= { r : RelType' R // r.arity = some n }

-- lemma RelType'.sig.cons {R : Type} [TupleSet R] {m : Shared.mult} :
--   (@RelType'.sig R _ m).arity = some 1 := by dsimp[RelType'.arity]
def RelType.sig (R : Type) [TupleSet R] (m : Shared.mult) :=
  @Subtype.mk _ (λ r => r.arity = some 1) (@RelType'.sig R _ m) (by dsimp[RelType'.arity])

def RelType.unary_rel (R : Type) [TupleSet R] (m : Shared.mult) (r : R) (h : HasArity.hasArity r 1):=
  @Subtype.mk _ (λ r => r.arity = some 1) (@RelType'.unary_rel R _ m r h) (by dsimp[RelType'.arity])

def RelType.rel (R : Type) [TupleSet R] (r : R) (n : ℕ) (h : HasArity.hasArity r n):=
  @Subtype.mk _ (λ r => r.arity = some n) (@RelType'.rel R _ r n h) (by dsimp[RelType'.arity])

def RelType.constant (R : Type) [TupleSet R] (c : R) (n : ℕ) (h : HasArity.hasArity c n) :=
  @Subtype.mk _ (λ r => r.arity = some n) (@RelType'.constant R _ c n h) (by dsimp[RelType'.arity])

def RelType.none (R : Type) [TupleSet R] (n : ℕ) :=
  @Subtype.mk _ (λ r => r.arity = some n) (@RelType'.constant R _ ((@SetConstants.none R _)) n arity_none) (by dsimp)

def RelType.univ (R : Type) [TupleSet R] :=
  @Subtype.mk _ (λ r => r.arity = some 1) (@RelType'.constant R _ ((@RelConstants.univ R _)) 1 arity_univ) (by dsimp)

def RelType.iden (R : Type) [TupleSet R] :=
  @Subtype.mk _ (λ r => r.arity = some 2) (@RelType'.constant R _ ((@RelConstants.iden R _)) 2 arity_iden) (by dsimp)

@[simp]
lemma RelType'.arity.cons {R : Type} [TupleSet R] {n : ℕ} (t : RelType R n) : t.1.arity = n := by
  cases t with
  | mk val property => dsimp[RelType'.arity]; trivial

def RelType.arity {R : Type} [TupleSet R] {n : ℕ} (t : RelType R n) := n
lemma RelType.arity.cons {R : Type} [TupleSet R] {n : ℕ} (t : RelType R n) : t.arity = n := by
  cases t with
  | mk val property => dsimp[arity]

def RelType.complex {R : Type} [TupleSet R] {n1 : ℕ} (t1 : RelType R n1) (m1 m2 : Shared.mult) {n2 : ℕ} (t2 : RelType R n2) :=
  @Subtype.mk _ (λ r => r.arity = some (n1 + n2)) (@RelType'.complex R _ t1.1 m1 m2 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n : ℕ) : Intersect (RelType R n) where
  intersect t1 t2 := Subtype.mk (RelType'.intersect t1.1 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n : ℕ) : Add (RelType R n) where
  add t1 t2 := Subtype.mk (RelType'.add t1.1 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n : ℕ) : Sub (RelType R n) where
  sub t1 t2 := Subtype.mk (RelType'.sub t1.1 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n : ℕ) : Append (RelType R n) where
  append t1 t2 := Subtype.mk (RelType'.append t1.1 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
    HCartprod (RelType R n1) (RelType R n2) (outParam (RelType R (n1 + n2))) where
      hCartprod (t1 : RelType R n1) (t2 : RelType R n2) :=
        Subtype.mk (RelType'.cartprod t1.1 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
    HDotjoin (RelType R (n1 + 1)) (RelType R (n2 + 1)) ( (RelType R (n1 + n2))) where
      hDotjoin (t1 : RelType R (n1 +1)) (t2 : RelType R (n2 + 1)):=
        Subtype.mk (RelType'.dotjoin t1.1 t2.1) (by simp ; ring_nf ; rw[add_assoc, add_comm] ; simp)

instance (R : Type) [TupleSet R] : Transclos (RelType R 2) where
  transclos t := Subtype.mk (RelType'.transclos t.1) (by simp)
instance (R : Type) [TupleSet R] : ReflTransclos (RelType R 2) where
  rtransclos t := Subtype.mk (RelType'.transclos t.1) (by simp)
instance (R : Type) [TupleSet R] : Transpose (RelType R 2) where
  transpose t := Subtype.mk (RelType'.transpose t.1) (by simp)

instance (R : Type) [TupleSet R] (n : ℕ):
    HDomRestr (RelType R 1) (RelType R n) (outParam (RelType R n)) where
      hDomrestr (t1 : RelType R 1) (t2 : RelType R n) :=
        Subtype.mk (RelType'.domrestr t1.1 t2.1) (by simp)
instance (R : Type) [TupleSet R] (n : ℕ):
    HRangeRestr (RelType R n) (RelType R 1) (outParam (RelType R n)) where
      hRangerestr (t1 : RelType R n) (t2 : RelType R 1) :=
        Subtype.mk (RelType'.rangerestr t1.1 t2.1) (by simp)

def RelType.ifThenElse {R : Type} [TupleSet R] {n : ℕ} (t1 t2 : RelType R n) :=
  @Subtype.mk _ (λ r => r.arity = some n) (RelType'.if_then_else t1.1 t2.1) (by simp)


instance [TupleSet R] {n : ℕ}: Arity (RelType R n) where
  arity             := n
  hasArity _ n'     := n = n'
  arity_consistent  := by simp
