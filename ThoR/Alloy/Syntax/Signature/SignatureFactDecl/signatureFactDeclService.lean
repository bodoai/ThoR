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
    : factDecl :=
      match sfd with
          | `(signatureFactDecl| $p:property) =>
                property.toType
                  defaultName.toName
                  p
                  signatureName
                  signatureRelationNames

          | _ => default

end Alloy.signatureFactDecl
