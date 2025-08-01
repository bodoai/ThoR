/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
note that dotjoin is in a different file to make use of precendece in expr
-/
import ThoR.Basic
import ThoR.Relation.Set
import ThoR.Relation.TupleSet
import ThoR.Relation.Rel
import ThoR.Alloy.Exceptions.NoMatchImplementedException
open Lean
open ThoR
namespace Shared

  /--
  This inductive type represents binary operations between relations
  -/
  inductive binRelOp
    | union -- +
    | intersection -- &
    | difference -- -
    | overwrite -- ++
    | domain_restriction -- <:
    | range_restriction -- :>
  deriving Repr

  /--
  This syntax represents binary operations between relations
  -/
  declare_syntax_cat binRelOp
  abbrev BinRelOp := TSyntax `binRelOp
  syntax "+" : binRelOp
  syntax "-" : binRelOp
  syntax "&" : binRelOp
  syntax "++" : binRelOp
  syntax "<:" : binRelOp
  syntax ":>" : binRelOp

  instance : ToString binRelOp where
    toString : binRelOp -> String
      | binRelOp.union => "+"
      | binRelOp.intersection => "&"
      | binRelOp.difference => "-"
      | binRelOp.overwrite => "++"
      | binRelOp.domain_restriction => "<:"
      | binRelOp.range_restriction => ":>"

  instance : BEq binRelOp where
    beq : binRelOp -> binRelOp -> Bool
      | binRelOp.union,  binRelOp.union => true
      | binRelOp.intersection,  binRelOp.intersection => true
      | binRelOp.difference,  binRelOp.difference => true
      | binRelOp.overwrite,  binRelOp.overwrite => true
      | binRelOp.domain_restriction,  binRelOp.domain_restriction => true
      | binRelOp.range_restriction,  binRelOp.range_restriction => true
      | _, _ => false
  namespace binRelOp

    /--
    Generates a string representation of the type
    -/
    def toString (op : binRelOp) : String := s!"{op}"

    def isDomainRestriction (op : binRelOp) : Bool :=
      match op with
        | binRelOp.domain_restriction => true
        | _ => false

    /--
    Generates a syntax representation of the type
    -/
    def toSyntax (op : binRelOp) : BinRelOp := Unhygienic.run do
      match op with
        | binRelOp.union => `(binRelOp| +)
        | binRelOp.intersection => `(binRelOp| &)
        | binRelOp.difference => `(binRelOp| -)
        | binRelOp.overwrite => `(binRelOp| ++)
        | binRelOp.domain_restriction => `(binRelOp| <:)
        | binRelOp.range_restriction => `(binRelOp| :>)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
      (op : binRelOp)
      : Term := Unhygienic.run do
        match op with
          | binRelOp.union => `($(mkIdent ``HAdd.hAdd))
          | binRelOp.intersection => `($(mkIdent ``HIntersect.hIntersect))
          | binRelOp.difference => `($(mkIdent ``HSub.hSub))
          | binRelOp.overwrite => `($(mkIdent ``HAppend.hAppend))
          | binRelOp.domain_restriction => `($(mkIdent ``HDomRestr.hDomrestr))
          | binRelOp.range_restriction => `($(mkIdent ``HRangeRestr.hRangerestr))

    /--
    Parses the given syntax to the type
    -/
    def toType
      (op : BinRelOp)
      : Except String binRelOp :=
        match op with
          | `(binRelOp| +)  => return binRelOp.union
          | `(binRelOp| &)  => return binRelOp.intersection
          | `(binRelOp| -)  => return binRelOp.difference
          | `(binRelOp| ++) => return binRelOp.overwrite
          | `(binRelOp| <:) => return binRelOp.domain_restriction
          | `(binRelOp| :>) => return binRelOp.range_restriction

          | syntx =>
            throwNoMatchImplemented "binRelOp.toType" syntx

  end binRelOp

end Shared
