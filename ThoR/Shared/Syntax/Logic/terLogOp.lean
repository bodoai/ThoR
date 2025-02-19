/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

open Lean
namespace Shared

  /--
  This inductive type represents tertiary logic operations
  -/
  inductive terLogOp
    | ifelse
  deriving Repr, BEq

  -- the syntax is to be found in formula beacause of the special syntax

  instance : ToString terLogOp where
    toString : terLogOp -> String
      | terLogOp.ifelse => "ifelse"

  namespace terLogOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : terLogOp) : String := ToString.toString op

    /--
    Used to write the ifelse to a term
    -/
    def myIfElse (a b c : Prop) := (a -> b) /\ ((Not a) -> c)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : terLogOp) : TSyntax `term := Unhygienic.run do
      match op with
        | terLogOp.ifelse => `($(mkIdent ``myIfElse))

  end terLogOp

end Shared
