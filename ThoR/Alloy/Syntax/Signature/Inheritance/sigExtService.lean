/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Signature.Inheritance.sigExt
import ThoR.Shared.Syntax.TypeExpr.typeExprService

namespace Alloy.sigExt

  /--
  Gets the required variables for the extensions
  -/
  def getReqVariables (se : sigExt) : List (String) :=
    match se with
      | sigExt.extends ext => ext.type.getReqVariables
      | sigExt.in extIn => extIn.type.getReqVariables
      | sigExt.none => []

end Alloy.sigExt
