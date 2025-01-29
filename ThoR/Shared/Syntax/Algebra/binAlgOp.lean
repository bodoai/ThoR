/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

open Lean

namespace Shared

  /--
  This inductive type represents an binary operation between algebra expressions
  -/
  inductive binAlgOp
    | add -- + plus
    | sub -- - minus
    | mult -- * mul
    | div -- / div
    | rem -- rem
  deriving Repr, BEq

  /--
  This syntax represents an binary operation between algebra expressions
  -/
  declare_syntax_cat binAlgOp
  syntax "plus" : binAlgOp
  syntax "minus" : binAlgOp
  syntax "mul" : binAlgOp
  syntax "div" : binAlgOp
  syntax "rem" : binAlgOp

  instance : ToString binAlgOp where
    toString : binAlgOp -> String
      | binAlgOp.add => "plus"
      | binAlgOp.sub => "minus"
      | binAlgOp.mult => "mul"
      | binAlgOp.div => "div"
      | binAlgOp.rem => "rem"
  namespace binAlgOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : binAlgOp) : String := ToString.toString op

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
    (op : binAlgOp)
    : TSyntax `term := Unhygienic.run do
      match op with
        | binAlgOp.add => `($(mkIdent ``Add.add))
        | binAlgOp.sub => `($(mkIdent ``Sub.sub))
        | binAlgOp.mult => `($(mkIdent ``Mul.mul))
        | binAlgOp.div => `($(mkIdent ``Div.div))
        | binAlgOp.rem => `($(mkIdent ``Mod.mod))

    /--
    Parses the given syntax to the type
    -/
    def toType (op : TSyntax `binAlgOp) : binAlgOp :=
      match op with
        | `(binAlgOp| plus) => binAlgOp.add
        | `(binAlgOp| minus) => binAlgOp.sub
        | `(binAlgOp| mul) => binAlgOp.mult
        | `(binAlgOp| div) => binAlgOp.div
        | `(binAlgOp| rem) => binAlgOp.rem

        | _ => binAlgOp.add -- unreachable

  end binAlgOp

end Shared
