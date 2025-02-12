/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Signature.FieldDecl.fieldDecl
import ThoR.Shared.Syntax.TypeExpr.typeExprService

namespace Alloy.fieldDecl

  def insertModuleVariables
    (fd : fieldDecl)
    (moduleVariables openVariables : List (String))
    : fieldDecl :=
    {fd with type := fd.type.insertModuleVariables moduleVariables openVariables}

end Alloy.fieldDecl
