/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.SymbolTable.VarDecl.varDecl
import ThoR.Shared.Syntax.TypeExpr.typeExprService

namespace Alloy.varDecl

  def simplifyDomainRestrictions
    (vd : varDecl)
    (st : SymbolTable)
    : varDecl :=
      {vd with type := vd.type.simplifyDomainRestrictions st}

end Alloy.varDecl
