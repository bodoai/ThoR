/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Config
import ThoR.Relation.Rel

import ThoR.Alloy.Exceptions.NoMatchImplementedException

open ThoR Config
open Lean
namespace Shared

  /--
  This inductive type represents an alloy constant
  -/
  inductive constant where
    | none
    | univ
    | iden
  deriving Repr

  /--
  This syntax represents an alloy constant
  -/
  declare_syntax_cat constant
  abbrev Constant := TSyntax `constant
  syntax ("univ"): constant
  syntax ("none") : constant
  syntax ("iden") : constant

  instance : ToString constant where
    toString :  constant -> String
      | constant.none => "none"
      | constant.iden => "iden"
      | constant.univ => "univ"

  instance : BEq constant where
    beq : constant -> constant -> Bool
      | constant.univ, constant.univ => true
      | constant.iden, constant.iden => true
      | constant.none, constant.none => true
      | _, _ => false

  instance : Inhabited constant where
    default := constant.none
  namespace constant

    /--
    Generates a string representation of the type
    -/
    def toString (c : constant) : String := s!"{c}"

    /--
    Generates syntax corosponding to the type
    -/
    def toSyntax (c : constant) : Constant := Unhygienic.run do
      match c with
        | constant.none => `(constant| none)
        | constant.iden => `(constant| iden)
        | constant.univ => `(constant| univ)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
      (c : constant)
      : Term := Unhygienic.run do
        match c with
          | constant.none =>
            `($(mkIdent ``Rel.constant.none) $(baseType.ident))
          | constant.univ =>
            `($(mkIdent ``Rel.constant.univ) $(baseType.ident))
          | constant.iden =>
            `($(mkIdent ``Rel.constant.iden) $(baseType.ident))

    /--
    Parses the given syntax to the type
    -/
    def toType
      (c : Constant)
      : Except String constant :=
        match c with
          | `(constant| none) => return constant.none
          | `(constant| iden) => return constant.iden
          | `(constant| univ) => return constant.univ

          | syntx =>
            throwNoMatchImplemented "constant.toType" syntx

  end constant

end Shared
