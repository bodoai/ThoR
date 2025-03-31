/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.AssertDecl.assertDecl
import ThoR.Alloy.Syntax.Property.propertyService

namespace Alloy.assertDecl

  /-- Generates a type representation from the TSyntax -/
  def toType (ad : AssertDecl) : assertDecl :=
    match ad with
      | `(assertDecl| assert $name:extendedIdent $p:property) =>
          property.toType (extendedIdent.toName name) p

      | _ => default

  /--
  Extracts all required definitions (i.e. references to preds)
  from the formulas of the type
  -/
  def getReqDefinitions
    (ad : assertDecl)
    : List (String) := Id.run do
      let mut result : List (String) := []

      for form in ad.formulas do
        result := result ++ form.getReqDefinitions

      return result

  /--
  Extracts all required variables from the formulas of the type
  -/
  def getReqVariables
    (ad : assertDecl)
    : List (String) := Id.run do
      let mut result : List (String) := []

      for form in ad.formulas do
        result := result ++ form.getReqVariables

      return result

  def simplifyDomainRestrictions
    (ad : assertDecl)
    (st : SymbolTable)
    : assertDecl :=
    let formulas := ad.formulas.map fun f => f.simplifyDomainRestrictions st
    {ad with formulas := formulas}

  def insertModuleVariables
    (ad : assertDecl)
    (moduleVariables openVariables : List (String))
    : assertDecl :=
    let formulas := ad.formulas.map
      fun f => f.insertModuleVariables moduleVariables openVariables
    {ad with formulas := formulas}

  def replaceThisCalls
    (ad : assertDecl)
    (moduleName : String)
    : assertDecl :=
    let formulas :=
      ad.formulas.map fun f => f.replaceThisCalls moduleName
    {ad with formulas := formulas}

end Alloy.assertDecl
