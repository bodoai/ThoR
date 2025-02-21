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

inductive RelType (R : Type) [TupleSet R]: ℕ -> Type :=
  | sig (m : Shared.mult) : n = 1 → RelType R n
  | unary_rel (m : Shared.mult) (r : R) : n = 1 → HasArity.hasArity r 1 -> RelType R n
  | rel (r : R): HasArity.hasArity r n → RelType R n
  | constant (c : R) : HasArity.hasArity c n → RelType R n
  | complex
    (t1 : RelType R n1) (m1 m2 : Shared.mult) (t2 : RelType R n2):
      RelType R (n1 + n2)
  | intersect (t1 : RelType R n) (t2 : RelType R n):
      RelType R n
  | add (t1 : RelType R n) (t2 : RelType R n):
      RelType R n
  | sub (t1 : RelType R n) (t2 : RelType R n):
      RelType R n
  | append (t1 : RelType R n) (t2 : RelType R n):
      RelType R n
  | cartprod (t1 : RelType R n1) (t2 : RelType R n2):
      RelType R (n1 + n2)
  | dotjoin (t1 : RelType R (n1+1)) (t2 : RelType R (n2+1)):
      RelType R (n1+n2)
  | transclos (t : RelType R 2):
      RelType R 2
  | reftransclos (t : RelType R 2):
      RelType R 2
  | transpose (t : RelType R 2):
      RelType R 2
  | domrestr (t1 : RelType R 1) (t2 : RelType R n):
      RelType R n
  | rangerestr (t1 : RelType R n) (t2 : RelType R 1):
      RelType R n

macro "op_inst" name:ident typeClass:ident op:ident : command
=> do
    `(
    instance (R : Type) [TupleSet R] (n : ℕ):
        $typeClass (RelType R n) where
            $op := $name
    )
op_inst RelType.intersect Intersect intersect
op_inst RelType.add Add add
op_inst RelType.sub Sub sub
op_inst RelType.append Append append

instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
    HCartprod (RelType R n1) (RelType R n2) (outParam (RelType R (n1 + n2))) where
        hCartprod (t1 : RelType R n1) (t2 : RelType R n2):=
        RelType.cartprod t1 t2

instance (R : Type) [TupleSet R] (n1 n2 : ℕ):
    HDotjoin (RelType R (n1 +1)) (RelType R (n2+1)) (outParam (RelType R (n1 + n2))) where
        hDotjoin (t1 : RelType R (n1 +1)) (t2 : RelType R (n2 + 1)):=
        RelType.dotjoin t1 t2

instance (R : Type) [TupleSet R]: Transclos (RelType R 2) where
        transclos := RelType.transclos
instance (R : Type) [TupleSet R]: ReflTransclos (RelType R 2) where
        rtransclos := RelType.reftransclos
instance (R : Type) [TupleSet R]: Transpose (RelType R 2) where
        transpose := RelType.transpose

macro "unop_inst" name:ident typeClass:ident op:ident : command
=> do
    `(
    instance (R : Type) [TupleSet R] (n : ℕ):
        $typeClass (RelType R n) where
            $op := $name
    )

-- instance (R : Type) [TupleSet R] (n : ℕ):
--     Add (RelType R n) where
--         add := RelType.add

instance [TupleSet R] {n : ℕ}: Arity (RelType R n) where
  arity             := n
  hasArity _ n'     := n = n'
  arity_consistent  := by simp
