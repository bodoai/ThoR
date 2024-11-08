/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Relation.Set
import ThoR.Relation.TupleSet
import ThoR.Relation.Rel
open Lean
open ThoR

namespace Shared

  /--
  This inductive type represents a dotjoin relations
  -/
  inductive dotjoin
    | dot_join -- .
  deriving Repr

  /--
  This syntax represents a dotjoin relations
  -/
  declare_syntax_cat dotjoin
  syntax:60 "." : dotjoin
  syntax:60 "⋈" : dotjoin

  instance : ToString dotjoin where
    toString : dotjoin -> String
      | dotjoin.dot_join => "."

  instance : BEq dotjoin where
    beq : dotjoin -> dotjoin -> Bool
      | dotjoin.dot_join,  dotjoin.dot_join => true

  namespace dotjoin

    /--
    Generates a string representation of the type
    -/
    def toString (dj : dotjoin) : String := s!"{dj}"

    /--
    Generates a syntax representation of the type
    -/
    def toSyntax (dj : dotjoin) : TSyntax `dotjoin := Unhygienic.run do
      match dj with
        | dotjoin.dot_join => `(dotjoin| .)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
      (dj : dotjoin)
      : TSyntax `term := Unhygienic.run do
        match dj with
          | dotjoin.dot_join => `($(mkIdent ``HDotjoin.hDotjoin))

    /--
    Parses the given syntax to the type
    -/
    def toType (op : TSyntax `dotjoin) : dotjoin :=
      match op with
        | `(dotjoin| .)  => dotjoin.dot_join
        | `(dotjoin| ⋈)  => dotjoin.dot_join
        | _ => dotjoin.dot_join -- unreachable

  end dotjoin

end Shared
