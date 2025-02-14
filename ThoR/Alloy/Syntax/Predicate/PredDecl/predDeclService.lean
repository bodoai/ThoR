/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Predicate.PredDecl.predDecl
import ThoR.Alloy.Syntax.Predicate.PredArg.predArgService

namespace Alloy.predDecl

  def simplifyDomainRestrictions
    (pd : predDecl)
    (st : SymbolTable)
    : predDecl :=
    let args := pd.args.map fun arg => arg.simplifyDomainRestrictions st
    let forms := pd.forms.map fun f => f.simplifyDomainRestrictions st
    { pd with args := args, forms := forms}

end Alloy.predDecl
