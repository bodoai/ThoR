
/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Exceptions.NoMatchImplementedException

open Lean PrettyPrinter Delaborator SubExpr
namespace Shared

  /--
  This inductive type represents binary logic operations
  -/
  inductive binLogOp
    | or -- ||
    | and -- &&
    | equivalent -- <=>
    | implication -- =>
  deriving Repr, BEq

  /--
  This syntax represents binary logic operations
  -/
  declare_syntax_cat binLogOp
  abbrev BinLogOp := TSyntax `binLogOp

  syntax "||" : binLogOp
  syntax "or" : binLogOp

  syntax "&&" : binLogOp
  syntax "and" : binLogOp

  syntax "<=>" : binLogOp
  syntax "equivalent" : binLogOp

  syntax "=>" : binLogOp
  syntax "implies" : binLogOp

  instance : ToString binLogOp where
    toString : binLogOp -> String
      | binLogOp.or => "or"
      | binLogOp.and => "and"
      | binLogOp.equivalent => "equivalent"
      | binLogOp.implication => "implies"
  namespace binLogOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : binLogOp) : String := ToString.toString op

    /--
    Used to write the implication to a term
    -/
    def myImplication (a b : Prop) : Prop := a → b

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : binLogOp) : Term := Unhygienic.run do
      match op with
        | binLogOp.or => `($(mkIdent ``Or))
        | binLogOp.and => `($(mkIdent ``And))
        | binLogOp.equivalent => `($(mkIdent ``Iff))
        | binLogOp.implication => `($(mkIdent ``myImplication))

    /--
    Parses the given syntax to the type
    -/
    def toType
    (op : BinLogOp)
    : Except String binLogOp :=
      match op with
        | `(binLogOp| ||) => return binLogOp.or
        | `(binLogOp| or) => return binLogOp.or

        | `(binLogOp| &&) => return binLogOp.and
        | `(binLogOp| and) => return binLogOp.and

        | `(binLogOp| <=>) => return binLogOp.equivalent
        | `(binLogOp| equivalent) => return binLogOp.equivalent

        | `(binLogOp| =>) => return binLogOp.implication
        | `(binLogOp| implies) => return binLogOp.implication

        | syntx =>
          throwNoMatchImplemented "binLogOp.toType" syntx

  end binLogOp

end Shared
