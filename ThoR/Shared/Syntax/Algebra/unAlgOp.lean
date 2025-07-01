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
  This inductive type represents an unary algebra operator
  -/
  inductive unAlgOp
    | negation

  deriving Repr, BEq

  /--
  This syntax represents an unary algebra operator
  -/
  declare_syntax_cat unAlgOp
  abbrev UnAlgOp := TSyntax `unAlgOp
  syntax "-" : unAlgOp

  instance : ToString unAlgOp where
    toString : unAlgOp -> String
      | unAlgOp.negation => "-"
  namespace unAlgOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : unAlgOp) : String := ToString.toString op

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
    (op : unAlgOp)
    : Term := Unhygienic.run do
      match op with
        | unAlgOp.negation => `($(mkIdent ``Neg.neg))

    /--
    Parses the given syntax to the type
    -/
    def toType
      (op : UnAlgOp)
      : Except String unAlgOp := do
      match op with
        | `(unAlgOp| -) => return unAlgOp.negation

        | syntx =>
          throwNoMatchImplemented "unAlgOp.toType" syntx

  end unAlgOp

end Shared
