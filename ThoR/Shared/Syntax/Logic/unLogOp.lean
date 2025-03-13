/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

open Lean

namespace Shared

  /--
  This inductive type represents unary logic operations
  -/
  inductive unLogOp
    | not
  deriving Repr, BEq

  /--
  This syntax represents unary logic operations
  -/
  declare_syntax_cat unLogOp
  abbrev UnLogOp := TSyntax `unLogOp
  syntax "not" : unLogOp

  instance : ToString unLogOp where
    toString : unLogOp -> String
      | unLogOp.not => "not"
  namespace unLogOp
    /--
    Generates a string representation of the type
    -/
    def toString (op : unLogOp) : String := ToString.toString op

    /--
    Parses the given syntax to the type
    -/
    def toType (op : UnLogOp) : unLogOp :=
      match op with
        | `(unLogOp| not) => unLogOp.not

        | _ => unLogOp.not -- unreachable

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : unLogOp) : Term := Unhygienic.run do
      match op with
        | unLogOp.not => `($(mkIdent ``Not))

  end unLogOp

end Shared
