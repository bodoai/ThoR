
/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

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
    private def myImplication (a b : Prop) : Prop := a → b

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : binLogOp) : TSyntax `term := Unhygienic.run do
      match op with
        | binLogOp.or => `($(mkIdent ``Or))
        | binLogOp.and => `($(mkIdent ``And))
        | binLogOp.equivalent => `($(mkIdent ``Iff))
        | binLogOp.implication => `($(mkIdent ``myImplication))

    /--
    Parses the given syntax to the type
    -/
    def toType (op : TSyntax `binLogOp) : binLogOp :=
      match op with
        | `(binLogOp| ||) => binLogOp.or
        | `(binLogOp| or) => binLogOp.or

        | `(binLogOp| &&) => binLogOp.and
        | `(binLogOp| and) => binLogOp.and

        | `(binLogOp| <=>) => binLogOp.equivalent
        | `(binLogOp| equivalent) => binLogOp.equivalent

        | `(binLogOp| =>) => binLogOp.implication
        | `(binLogOp| implies) => binLogOp.implication

        | _ => binLogOp.or -- unreachable

  end binLogOp

end Shared
