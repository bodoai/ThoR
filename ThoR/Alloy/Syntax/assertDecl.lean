/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Syntax.property
import ThoR.Shared.Syntax.formula

open Lean
open Shared

namespace Alloy

  /--
  A type representation of an assert declaration. It is projected on `property`
  -/
  def assertDecl := property
  deriving Repr

  -- would be prettier to call the default of property
  instance : Inhabited assertDecl where
    default := {name := "Empty", formulas := []}

  /--
  A syntax repreaentation of an assert declaration.
  -/
  declare_syntax_cat assertDecl
  syntax "assert " ident property : assertDecl

  instance : ToString assertDecl where
    toString (ad : assertDecl) : String :=
      s!"assert : {property.toString ad}"

  namespace assertDecl

    /-- Generates a String representation from the type -/
    def toString (ad : assertDecl) : String := ToString.toString ad

    /-- Generates a type representation from the TSyntax -/
    def toType (ad : TSyntax `assertDecl) : assertDecl :=
      match ad with
        | `(assertDecl| assert $name:ident $p:property) =>
           property.toType name p

        | _ => default

    /--
    Extracts all required definitions (i.e. references to preds)
    from the formulas of the type
    -/
    def getReqDefinitions
      (ad : assertDecl)
      : List (String) := Id.run do
        let mut result : List (String) := []

        for form in ad.formulas do
          result := result ++ form.getReqDefinitions

        return result

    /--
    Extracts all required variables from the formulas of the type
    -/
    def getReqVariables
      (ad : assertDecl)
      : List (String) := Id.run do
        let mut result : List (String) := []

        for form in ad.formulas do
          result := result ++ form.getReqVariables

        return result

  end assertDecl

end Alloy
