/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.FactDecl.factDecl
import ThoR.Alloy.Syntax.Property.propertyService

namespace Alloy.factDecl

  /-- Generates a type representation from the TSyntax -/
  def toType
    (defaultName : String)
    (fd: FactDecl)
    : Except String factDecl := do
      match fd with
          --with name
        | `(factDecl| fact $name:extendedIdent $p:property) =>
              return ← property.toType (extendedIdent.toName name) p

          -- without name
          | `(factDecl| fact $p:property) =>
              return ← property.toType defaultName.toName p

          | syntx =>
            throw s!"No match implemented in factDeclService.toType for '{syntx}'"

  /--
  Extracts all required definitions (i.e. references to preds)
  from the formulas of the type
  -/
  def getReqDefinitions
    (fd : factDecl)
    : List (String) := Id.run do
      let mut result : List (String) := []

      for form in fd.formulas do
        result := result ++ form.getReqDefinitions

      return result

  /--
  Extracts all required variables from the formulas of the type
  -/
  def getReqVariables
    (fd : factDecl)
    : List (String) := Id.run do
      let mut result : List (String) := []

      for form in fd.formulas do
        result := result ++ form.getReqVariables

      return result

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

  def getFunctionCalls
    (fd : factDecl)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (Shared.expr × List (String × List (varDecl))))) := do
      let mut result := []
      for form in fd.formulas do
        result := result.append (← form.getFunctionCalls callableFunctions callableVariables)
      return result

end Alloy.factDecl
