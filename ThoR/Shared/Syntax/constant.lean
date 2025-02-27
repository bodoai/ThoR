/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Config
import ThoR.Relation.Rel

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
    def toSyntax (c : constant) : TSyntax `constant := Unhygienic.run do
      match c with
        | constant.none => `(constant| none)
        | constant.iden => `(constant| iden)
        | constant.univ => `(constant| univ)

    /--
    Generates a Lean term corosponding with the type
    -/
    def toTerm
      (c : constant)
      : TSyntax `term := Unhygienic.run do
        match c with
          | constant.none =>
            `($(mkIdent ``Rel.constant.none) $(baseType.ident))
          | constant.univ =>
            `($(mkIdent ``Rel.constant.univ) $(baseType.ident))
          | constant.iden =>
            `($(mkIdent ``Rel.constant.iden) $(baseType.ident))

    open ThoR.Rel.constant
    /--
    Generates a Lean term corosponding with the type
    -/
    def fromTerm
      (c : Term)
      : Except String constant := Unhygienic.run do
        let ms ←  `($(mkIdent `univ))
        if c == ms then
          return Except.ok constant.univ

        match c with
          | `(``ThoR.Rel.constant.none $_) =>
            return Except.ok constant.none
          | `(``ThoR.Rel.constant.univ $_) =>
            return Except.ok constant.univ
          | `(``ThoR.Rel.constant.univ) =>
            return Except.ok constant.univ
          | `(`univ $_) =>
            return Except.ok constant.univ
          | `(`univ) =>
            return Except.ok constant.univ
          | `(constant| univ) =>
            return Except.ok constant.univ
          | `(ThoR.Rel.constant.univ) =>
            return Except.ok constant.univ
          | `(ThoR.Rel.constant.univ $_) =>
            return Except.ok constant.univ
          | `(``ThoR.Rel.constant.iden $_) =>
            return Except.ok constant.iden
          | a => return (Except.error s!"YYY {a.raw.prettyPrint}")

    /--
    Parses the given syntax to the type
    -/
    def toType (c : TSyntax `constant) : constant :=
      match c with
        | `(constant| none) => constant.none
        | `(constant| iden) => constant.iden
        | `(constant| univ) => constant.univ

        | _ => constant.none -- unreachable

  end constant

end Shared
