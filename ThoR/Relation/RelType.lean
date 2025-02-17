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
  | dotjoin (t1 : RelType' R) (t2 : RelType' R) :  RelType' R

-- Why define checkArityEq as a macro and not as a function?
-- Putting this into a macro makes it easier to implement RelType'.arity.
-- Putting this into a function requires an explicit proof for termination of arity.
macro "checkArityEq" "(" f:term ", " t1:term ", " t2:term ")": term =>
`(do
    let n1 ← ($f $t1)
    let n2 ← ($f $t2)
    if (n1 = n2)
    then return n1
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
  | dotjoin t1 t2 => do
                      let n1 ← t1.arity
                      let n2 ← t2.arity
                      if (n1 > 0 ∧ n2 >0)
                      then return n1 + n2 - 2
                      else none

  -- | add (t1 : RelType' R) (t2 : RelType' R): RelType' R
  -- | sub (t1 : RelType R n) (t2 : RelType R n):
  --     RelType R n
  -- | append (t1 : RelType R n) (t2 : RelType R n):
  --     RelType R n
  -- | cartprod (t1 : RelType R n1) (t2 : RelType R n2):
  --     RelType R (n1 + n2)
  -- | transclos (t : RelType R 2):
  --     RelType R 2
  -- | reftransclos (t : RelType R 2):
  --     RelType R 2
  -- | transpose (t : RelType R 2):
  --     RelType R 2
  -- | domrestr (t1 : RelType R 1) (t2 : RelType R n):
  --     RelType R n
  -- | rangerestr (t1 : RelType R n) (t2 : RelType R 1):
  --     RelType R n

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

@[simp]
lemma RelType'.arity.cons {R : Type} [TupleSet R] {n : ℕ} (t : RelType R n) : t.1.arity = n := by
  cases t with
  | mk val property => dsimp[RelType'.arity]; trivial

def RelType.arity {R : Type} [TupleSet R] {n : ℕ} (t : RelType R n) := n
lemma RelType.arity.cons {R : Type} [TupleSet R] {n : ℕ} (t : RelType R n) : t.arity = n := by
  cases t with
  | mk val property => dsimp[arity]

def RelType.complex {R : Type} [TupleSet R] {n1 : ℕ} (t1 : RelType' R) (h1 : t1.arity = some n1) (m1 m2 : Shared.mult) {n2 : ℕ} (t2 : RelType' R) (h2 : t2.arity = some n2):=
  @Subtype.mk _ (λ r => r.arity = some (n1 + n2)) (@RelType'.complex R _ t1 m1 m2 t2) (by simp; rw[h1,h2]; simp)

instance (R : Type) [TupleSet R] (n : ℕ) : Intersect (RelType R n) where
  intersect t1 t2 := Subtype.mk (RelType'.intersect t1.1 t2.1) (by simp)

instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
    HDotjoin (RelType R (n1 + 1)) (RelType R (n2 + 1)) (outParam (RelType R (n1 + n2))) where
      hDotjoin (t1 : RelType R (n1 +1)) (t2 : RelType R (n2 + 1)):=
        Subtype.mk (RelType'.dotjoin t1.1 t2.1) (by simp ; ring_nf ; rw[add_assoc, add_comm] ; simp)

-- macro "op_inst" name:ident typeClass:ident op:ident : command
-- => do
--     `(
--     instance (R : Type) [TupleSet R] (n : ℕ):
--         $typeClass (RelType R n) where
--             $op := $name
--     )
-- op_inst RelType.intersect Intersect intersect
-- op_inst RelType.add Add add
-- op_inst RelType.sub Sub sub
-- op_inst RelType.append Append append

-- instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
--     HCartprod (RelType R n1) (RelType R n2) (outParam (RelType R (n1 + n2))) where
--         hCartprod (t1 : RelType R n1) (t2 : RelType R n2):=
--         RelType.cartprod t1 t2

-- instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
--     HDotjoin (RelType R (n1 +1)) (RelType R (n2+1)) (outParam (RelType R (n1 + n2))) where
--         hDotjoin (t1 : RelType R (n1 +1)) (t2 : RelType R (n2 + 1)):=
--         RelType.dotjoin t1 t2

-- instance (R : Type) [TupleSet R]: Transclos (RelType R 2) where
--         transclos := RelType.transclos
-- instance (R : Type) [TupleSet R]: ReflTransclos (RelType R 2) where
--         rtransclos := RelType.reftransclos
-- instance (R : Type) [TupleSet R]: Transpose (RelType R 2) where
--         transpose := RelType.transpose

-- macro "unop_inst" name:ident typeClass:ident op:ident : command
-- => do
--     `(
--     instance (R : Type) [TupleSet R] (n : ℕ):
--         $typeClass (RelType R n) where
--             $op := $name
--     )

-- instance (R : Type) [TupleSet R] (n : ℕ):
--     Add (RelType R n) where
--         add := RelType.add

instance [TupleSet R] {n : ℕ}: Arity (RelType R n) where
  arity             := n
  hasArity _ n'     := n = n'
  arity_consistent  := by simp
