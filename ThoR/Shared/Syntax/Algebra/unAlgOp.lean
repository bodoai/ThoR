/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

open Lean

namespace Shared

  /--
  This inductive type represents an unary algebra operator
  -/
  inductive unAlgOp
    | negation

  deriving Repr

  /--
  This syntax represents an unary algebra operator
  -/
  declare_syntax_cat unAlgOp
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
    : TSyntax `term := Unhygienic.run do
      match op with
        | unAlgOp.negation => `($(mkIdent ``Neg.neg))

    /--
    Parses the given syntax to the type
    -/
    def toType (op : TSyntax `unAlgOp) : unAlgOp :=
      match op with
        | `(unAlgOp| -) => unAlgOp.negation

        | _ => unAlgOp.negation -- unreachable

  end unAlgOp

end Shared
