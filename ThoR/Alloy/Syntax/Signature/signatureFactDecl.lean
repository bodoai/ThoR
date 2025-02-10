/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.FactDecl.factDecl
import ThoR.Alloy.Syntax.AssertDecl.assertDecl

open Lean

namespace Alloy

  /--
  A type representation of an signature fact declaration. It is projected on `fact declaration`
  -/
  def signatureFactDecl := factDecl
  deriving Repr

  -- would be prettier to call the default of property
  instance : Inhabited signatureFactDecl where
    default := {name := "Empty", formulas := []}

  /--
  A syntax repreaentation of an fact declaration.
  -/
  declare_syntax_cat signatureFactDecl
  syntax property : signatureFactDecl

  namespace signatureFactDecl

    /--
    Generates a factDeclaration from the signature fact. Accomodating the specifics
    such as creating a quantification.
    -/
    def toType
      (defaultName : String)
      (fd: TSyntax `signatureFactDecl)
      (signatureName : String)
      (signatureRelationNames : List String)
      : factDecl :=
        match fd with
            | `(signatureFactDecl| $p:property) =>
                  property.toType
                    defaultName.toName
                    p
                    signatureName
                    signatureRelationNames

            | _ => default

  end signatureFactDecl

end Alloy
