/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

open Lean

namespace Shared

  /--
  This inductive type represents compare operations between algebra expression
  -/
  inductive algCompareOp
    | lt -- <
    | gt -- >
    | eq -- =
    | leq -- =< or <=
    | geq -- >= or =>
  deriving Repr

  /--
  This syntax represents compare operations between algebra expression
  -/
  declare_syntax_cat algCompareOp
  syntax "<" : algCompareOp
  syntax ">" : algCompareOp
  syntax "=" : algCompareOp
  syntax "=<" : algCompareOp
  syntax ">=" : algCompareOp

  instance : ToString algCompareOp where
    toString : algCompareOp -> String
      | algCompareOp.lt => "<"
      | algCompareOp.gt => ">"
      | algCompareOp.eq => "="
      | algCompareOp.leq => "=<"
      | algCompareOp.geq => ">="
  namespace algCompareOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : algCompareOp) : String := ToString.toString op

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : algCompareOp) : TSyntax `term := Unhygienic.run do
      match op with
        | algCompareOp.lt => `($(mkIdent ``LT.lt))
        | algCompareOp.gt => `($(mkIdent ``GT.gt))
        | algCompareOp.eq => `($(mkIdent ``Eq))
        | algCompareOp.leq => `($(mkIdent ``LE.le))
        | algCompareOp.geq => `($(mkIdent ``GE.ge))

    /--
    Parses the given syntax to the type
    -/
    def toType (op: TSyntax `algCompareOp) : algCompareOp :=
      match op with
        | `(algCompareOp| <) => algCompareOp.lt
        | `(algCompareOp| >) => algCompareOp.gt
        | `(algCompareOp| =) => algCompareOp.eq
        | `(algCompareOp| =<) => algCompareOp.leq
        | `(algCompareOp| >=) => algCompareOp.geq

        | _ => algCompareOp.eq -- unreachable

  end algCompareOp

end Shared