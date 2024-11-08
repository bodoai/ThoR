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
  deriving Repr

  /--
  This syntax represents unary logic operations
  -/
  declare_syntax_cat unLogOp
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
    def toType (op : TSyntax `unLogOp) : unLogOp :=
      match op with
        | `(unLogOp| not) => unLogOp.not

        | _ => unLogOp.not -- unreachable

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : unLogOp) : TSyntax `term := Unhygienic.run do
      match op with
        | unLogOp.not => `($(mkIdent ``Not))

  end unLogOp

end Shared
