/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.AssertDecl.assertDecl

namespace Alloy.assertDecl

  def simplifyDomainRestrictions
    (ad : assertDecl)
    (st : SymbolTable)
    : assertDecl :=
    let formulas := ad.formulas.map fun f => f.simplifyDomainRestrictions st
    {ad with formulas := formulas}

end Alloy.assertDecl
