/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Relation.Set
import ThoR.Relation.Rel
import ThoR.Alloy.Exceptions.NoMatchImplementedException

open Lean
open ThoR

namespace Shared

  /--
  This inductive type represents compare operations between relations
  -/
  inductive relCompareOp
    | in -- in
    | eq -- =
    | neq -- !=
  deriving Repr, BEq

  /--
  This syntax represents compare operations between relations
  -/
  declare_syntax_cat relCompareOp
  abbrev RelCompareOp := TSyntax `relCompareOp
  syntax "in" : relCompareOp
  syntax "=" : relCompareOp
  syntax "!=" :relCompareOp

  instance : ToString relCompareOp where
    toString : relCompareOp -> String
      | relCompareOp.in => "in" -- ThoR: ⊂
      | relCompareOp.eq => "="  -- ThoR: ≡
      | relCompareOp.neq => "!="

  namespace relCompareOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : relCompareOp) : String := ToString.toString op

    /--
    Parses the given syntax to the type
    -/
    def toType
      (op : RelCompareOp)
      : Except String relCompareOp :=
        match op with
          | `(relCompareOp| in) => return relCompareOp.in
          | `(relCompareOp| =) => return relCompareOp.eq
          | `(relCompareOp| !=) => return relCompareOp.neq

          | syntx =>
            throwNoMatchImplemented "relCompareOp.toType" syntx

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm (op : relCompareOp) : Term := Unhygienic.run do
      match op with
        | relCompareOp.in => `($(mkIdent ``HSubset.hSubset))
        | relCompareOp.eq => `($(mkIdent ``HEqual.hEqual))
        | relCompareOp.neq => `($(mkIdent ``HNEqual.hNEqual))

  end relCompareOp

end Shared
