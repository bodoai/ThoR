/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Signature.SigDecl.sigDecl
import ThoR.Alloy.Syntax.Signature.FieldDecl.fieldDeclService

namespace Alloy.sigDecl

  def insertModuleVariables
    (sd : sigDecl)
    (moduleVariables openVariables : List (String))
    : sigDecl :=
    let fieldDecls := sd.fieldDecls.map
      fun fd => fd.insertModuleVariables moduleVariables openVariables
    {sd with fieldDecls := fieldDecls}

end Alloy.sigDecl
