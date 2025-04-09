/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Signature.SignatureFactDecl.signatureFactDecl
import ThoR.Alloy.Syntax.Property.propertyService

namespace Alloy.signatureFactDecl

  /--
  Generates a factDeclaration from the signature fact. Accomodating the specifics
  such as creating a quantification.
  -/
  def toType
    (defaultName : String)
    (sfd: SignatureFactDecl)
    (signatureName : String)
    (signatureRelationNames : List String)
    : Except String factDecl := do
      match sfd with
          | `(signatureFactDecl| $p:property) =>
                return ← property.toType
                  defaultName.toName
                  p
                  signatureName
                  signatureRelationNames

          | syntx =>
            throw s!"No match implemented in \
            signatureFactDeclService.toType \
            for '{syntx}'"

end Alloy.signatureFactDecl
