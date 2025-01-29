/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
open Lean
namespace Shared

  /--
  This inductive type represents unary operations for a relation

  This operation returns a bool
  -/
  inductive unRelBoolOp
    | some
    | lone
    | one
    | no
  deriving Repr, BEq

  /--
  This syntax represents unary operations for a relation

  This operation returns a bool
  -/
  declare_syntax_cat unRelBoolOp
  syntax "some" : unRelBoolOp
  syntax "lone" : unRelBoolOp
  syntax "one" : unRelBoolOp
  syntax "no" : unRelBoolOp

  namespace unRelBoolOp

    instance : ToString unRelBoolOp where
    toString : unRelBoolOp -> String
      | unRelBoolOp.some => "some"
      | unRelBoolOp.lone => "lone"
      | unRelBoolOp.one => "one"
      | unRelBoolOp.no => "no"

    /--
    Generates a string representation of the type
    -/
    def toString (op: unRelBoolOp) : String := ToString.toString op

    /--
    Parses the given syntax to the type
    -/
    def toType (op : TSyntax `unRelBoolOp) : unRelBoolOp :=
      match op with
        | `(unRelBoolOp| some) => unRelBoolOp.some
        | `(unRelBoolOp| lone) => unRelBoolOp.lone
        | `(unRelBoolOp| one) => unRelBoolOp.one
        | `(unRelBoolOp| no) => unRelBoolOp.no

        | _ => unRelBoolOp.no -- unreachable

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : unRelBoolOp) : TSyntax `term := Unhygienic.run do
      match op with
        | unRelBoolOp.some => `($(mkIdent `ThoR.SetMultPredicates.some))
        | unRelBoolOp.lone => `($(mkIdent `ThoR.SetMultPredicates.lone))
        | unRelBoolOp.one =>  `($(mkIdent `ThoR.SetMultPredicates.one))
        | unRelBoolOp.no =>   `($(mkIdent `ThoR.SetMultPredicates.no))

  end unRelBoolOp

end Shared
