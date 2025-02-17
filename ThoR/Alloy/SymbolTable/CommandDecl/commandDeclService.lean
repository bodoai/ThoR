/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl
import ThoR.Shared.Syntax.Formula.formulaService
import ThoR.Alloy.Syntax.Predicate.PredArg.predArgService
import ThoR.Alloy.SymbolTable.VarDecl.varDeclService

namespace Alloy.commandDecl
  partial def simplifyDomainRestrictions
    (cd : commandDecl)
    (st : SymbolTable)
    : commandDecl :=
    let args := cd.args.map fun arg => (arg.1.simplifyDomainRestrictions st , arg.2)
    let formulas := cd.formulas.map fun f => f.simplifyDomainRestrictions st
    let predCalls := cd.predCalls.map fun pc =>
      ((pc.1.simplifyDomainRestrictions st),
        (pc.2.map fun l1 =>
          (l1.1,
            (l1.2.map fun l2 =>
              l2.map fun vd => vd.simplifyDomainRestrictions st))))
    let relationCalls := cd.relationCalls.map fun rc =>
      rc.map fun vd => vd.simplifyDomainRestrictions st
    let signatureCalls := cd.signatureCalls.map fun sc =>
      sc.map fun vd => vd.simplifyDomainRestrictions st

    commandDecl.mk
      (name := cd.name)
      (isPredicate := cd.isPredicate)
      (args := args)
      (formulas := formulas)
      (requiredDefs := cd.requiredDefs)
      (requiredVars := cd.requiredVars)
      (predCalls := predCalls)
      (relationCalls  := relationCalls)
      (signatureCalls := signatureCalls)

end Alloy.commandDecl
