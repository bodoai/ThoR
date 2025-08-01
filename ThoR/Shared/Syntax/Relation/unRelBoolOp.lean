/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Exceptions.NoMatchImplementedException
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
  abbrev UnRelBoolOp := TSyntax `unRelBoolOp
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
    def toType
      (op : UnRelBoolOp)
      : Except String unRelBoolOp :=
        match op with
          | `(unRelBoolOp| some) => return unRelBoolOp.some
          | `(unRelBoolOp| lone) => return unRelBoolOp.lone
          | `(unRelBoolOp| one) =>  return unRelBoolOp.one
          | `(unRelBoolOp| no) =>   return unRelBoolOp.no

          | syntx =>
            throwNoMatchImplemented "unRelBoolOp.toType" syntx

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : unRelBoolOp) : Term := Unhygienic.run do
      match op with
        | unRelBoolOp.some => `($(mkIdent `ThoR.SetMultPredicates.some))
        | unRelBoolOp.lone => `($(mkIdent `ThoR.SetMultPredicates.lone))
        | unRelBoolOp.one =>  `($(mkIdent `ThoR.SetMultPredicates.one))
        | unRelBoolOp.no =>   `($(mkIdent `ThoR.SetMultPredicates.no))

  end unRelBoolOp

end Shared
