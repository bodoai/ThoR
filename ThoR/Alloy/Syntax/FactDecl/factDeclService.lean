/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.FactDecl.factDecl

namespace Alloy.factDecl

  def simplifyDomainRestrictions
    (fd : factDecl)
    (st : SymbolTable)
    : factDecl :=
    let formulas := fd.formulas.map fun f => f.simplifyDomainRestrictions st
    {fd with formulas := formulas}

  def insertModuleVariables
    (fd : factDecl)
    (moduleVariables openVariables : List (String))
    : factDecl :=
    let formulas :=
      fd.formulas.map fun f => f.insertModuleVariables moduleVariables openVariables
    {fd with formulas := formulas}

  def replaceThisCalls
    (fd : factDecl)
    (moduleName : String)
    : factDecl :=
    let formulas :=
      fd.formulas.map fun f => f.replaceThisCalls moduleName
    {fd with formulas := formulas}

end Alloy.factDecl
