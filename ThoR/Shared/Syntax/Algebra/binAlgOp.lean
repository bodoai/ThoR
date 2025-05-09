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
  abbrev BinAlgOp := TSyntax `binAlgOp
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
    : Term := Unhygienic.run do
      match op with
        | binAlgOp.add => `($(mkIdent ``Add.add))
        | binAlgOp.sub => `($(mkIdent ``Sub.sub))
        | binAlgOp.mult => `($(mkIdent ``Mul.mul))
        | binAlgOp.div => `($(mkIdent ``Div.div))
        | binAlgOp.rem => `($(mkIdent ``Mod.mod))

    /--
    Parses the given syntax to the type
    -/
    def toType
      (op : BinAlgOp)
      : Except String binAlgOp :=
        match op with
          | `(binAlgOp| plus) => return binAlgOp.add
          | `(binAlgOp| minus) => return binAlgOp.sub
          | `(binAlgOp| mul) => return binAlgOp.mult
          | `(binAlgOp| div) => return binAlgOp.div
          | `(binAlgOp| rem) => return binAlgOp.rem

          | syntx =>
            throwNoMatchImplemented "binAlgOp.toType" syntx

  end binAlgOp

end Shared
