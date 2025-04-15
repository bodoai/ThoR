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
  deriving Repr, BEq

  /--
  This syntax represents compare operations between algebra expression
  -/
  declare_syntax_cat algCompareOp
  abbrev AlgCompareOp := TSyntax `algCompareOp
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

    def toSyntax (op : algCompareOp) : AlgCompareOp := Unhygienic.run do
      match op with
        | algCompareOp.lt => `(algCompareOp | <)
        | algCompareOp.gt => `(algCompareOp | >)
        | algCompareOp.eq => `(algCompareOp | =)
        | algCompareOp.leq => `(algCompareOp | =<)
        | algCompareOp.geq => `(algCompareOp | >=)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : algCompareOp) : Term := Unhygienic.run do
      match op with
        | algCompareOp.lt => `($(mkIdent ``LT.lt))
        | algCompareOp.gt => `($(mkIdent ``GT.gt))
        | algCompareOp.eq => `($(mkIdent ``Eq))
        | algCompareOp.leq => `($(mkIdent ``LE.le))
        | algCompareOp.geq => `($(mkIdent ``GE.ge))

    /--
    Parses the given syntax to the type
    -/
    def toType
      (op: AlgCompareOp)
      : Except String algCompareOp :=
        match op with
          | `(algCompareOp| <) => return algCompareOp.lt
          | `(algCompareOp| >) => return algCompareOp.gt
          | `(algCompareOp| =) => return algCompareOp.eq
          | `(algCompareOp| =<) => return algCompareOp.leq
          | `(algCompareOp| >=) => return algCompareOp.geq

          | syntx => throw s!"No match implemented in \
              algComapreOp.toType \
              for '{syntx}'"

  end algCompareOp

end Shared
