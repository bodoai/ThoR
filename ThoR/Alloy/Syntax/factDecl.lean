/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.assertDecl

open Lean

namespace Alloy

  /--
  A type representation of an fact declaration. It is projected on `property`
  -/
  def factDecl := property
  deriving Repr

  -- would be prettier to call the default of property
  instance : Inhabited factDecl where
    default := {name := "Empty", formulas := []}

  /--
  A syntax repreaentation of an fact declaration.
  -/
  declare_syntax_cat factDecl
  syntax "fact " (ident)? property : factDecl

  instance : ToString factDecl where
    toString (fd : factDecl) : String :=
      s!"fact : {property.toString fd}"
  namespace factDecl

    /-- Generates a String representation from the type -/
    def toString (fd : factDecl) : String := ToString.toString fd

    /-- Generates a type representation from the TSyntax -/
    def toType (defaultName : String) (fd: TSyntax `factDecl) : factDecl :=
      match fd with
          --with name
        | `(factDecl| fact $name:ident $p:property) =>
              property.toType name p

          -- without name
          | `(factDecl| fact $p:property) =>
                property.toType (mkIdent defaultName.toName) p

          | _ => default

    /--
    Extracts all required definitions (i.e. references to preds)
    from the formulas of the type
    -/
    def getReqDefinitions
      (fd : factDecl)
      : List (String) := Id.run do
        let mut result : List (String) := []

        for form in fd.formulas do
          result := result ++ form.getReqDefinitions

        return result

    /--
    Extracts all required variables from the formulas of the type
    -/
    def getReqVariables
      (fd : factDecl)
      : List (String) := Id.run do
        let mut result : List (String) := []

        for form in fd.formulas do
          result := result ++ form.getReqVariables

        return result

  end factDecl

end Alloy
