/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Relation.TupleSet
import ThoR.Relation.Rel

open Lean
open ThoR

namespace Shared

  /--
  This inductive type represents unary operations for a relation

  This operation returns a relation
  -/
  inductive unRelOp
    | transitive_closure -- ^
    | reflexive_closure -- *
    | transposition -- ~
  deriving Repr, BEq

  /--
  This syntax represents unary operations for a relation

  This operation returns a relation
  -/
  declare_syntax_cat unRelOp
  syntax "^" : unRelOp
  syntax "*" : unRelOp
  syntax "~" : unRelOp

  instance : ToString unRelOp where
    toString :  unRelOp -> String
      | unRelOp.transitive_closure => "^"
      | unRelOp.reflexive_closure => "*"
      | unRelOp.transposition => "~"

  instance : BEq unRelOp where
    beq : unRelOp -> unRelOp -> Bool
      | unRelOp.transitive_closure, unRelOp.transitive_closure => true
      | unRelOp.reflexive_closure, unRelOp.reflexive_closure => true
      | unRelOp.transposition, unRelOp.transposition => true
      | _, _ => false

  namespace unRelOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : unRelOp) : String := s!"{op}"

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax (op : unRelOp) : TSyntax `unRelOp := Unhygienic.run do
      match op with
        | unRelOp.transitive_closure => `(unRelOp| ^)
        | unRelOp.reflexive_closure => `(unRelOp| *)
        | unRelOp.transposition => `(unRelOp| ~)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
      (op : unRelOp)
      : TSyntax `term := Unhygienic.run do
        match op with
          | unRelOp.transitive_closure => `($(mkIdent ``HTransclos.hTransclos))
          | unRelOp.reflexive_closure => `($(mkIdent ``HReflTransclos.hRTransclos))
          | unRelOp.transposition => `($(mkIdent ``HTranspose.hTranspose))

    /--
    Parses the given syntax to the type
    -/
    def toType (op : TSyntax `unRelOp) : unRelOp :=
      match op with
        | `(unRelOp| ^) => unRelOp.transitive_closure
        | `(unRelOp| *) => unRelOp.reflexive_closure
        | `(unRelOp| ~) => unRelOp.transposition

        | _ => unRelOp.transitive_closure -- unreachable

  end unRelOp

end Shared
