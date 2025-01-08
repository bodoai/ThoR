/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
This file is used for semantic analysis of the AST and transforming its contents
to be better digestible for further computation and transformation into Lean.
-/
import ThoR.Basic
import ThoR.Shared.Syntax
import ThoR.Relation
import ThoR.Alloy.Syntax.AST
import ThoR.Alloy.SymbolTable.varDecl
import ThoR.Alloy.SymbolTable.commandDecl

import ThoR.Alloy.Syntax.Signature.signatureSeparator

open Lean
open Shared

namespace Alloy

  /--
  A structure representation of the symbol table (ST).
  -/
  structure SymbolTable where
    mk :: (blockName : String)
          (variableDecls : List (varDecl))
          (defDecls : List (commandDecl))
          (axiomDecls : List (commandDecl))
          (assertDecls : List (commandDecl))
          (requiredDecls : List (String))
  deriving Repr

  /--
  Reorders list of variable declarations such
  that the Lean requirement "declaration before use"
  is satisfied.

  Each varDecl contains the name `varDecl.name` of
  a to be declared variable and the list of all
  variable names `varDecl.requiredDecls` it depends on.

  Lean requires "declaration/definition before use", i.e.
  each symbol has to be declared, before it can be
  used. In Alloy signature declarations can contain
  references to signatures that are declared later
  (further down in the Alloy file).

  Therefore, the variable declarations which are
  derived from the Alloy block have to be ordered
  such that the Lean requirement "declaration before use"
  is satisfied.
  -/
  private def orderVarDecls (vds : List (varDecl)) : List (varDecl) := Id.run do
    let mut unorderd : List (varDecl) := vds
    let mut ordered : List (varDecl) := []

    let mut i := 0
    while !(unorderd.isEmpty) && (i < unorderd.length) do
      let vd? := unorderd.get? i
      if vd?.isSome then
        let vd := vd?.get!
        let mut allReqsAvariable := true

        if !(vd.requiredDecls.isEmpty) then
          let reqDecls : List (String) := vd.type.getReqVariables
          let definedNames := ordered.map fun (elem) => elem.name

          for reqDecl in reqDecls do
            if !(definedNames.contains reqDecl) then
              allReqsAvariable := false
              break

        if allReqsAvariable then
          ordered := ordered.concat vd
          unorderd := unorderd.eraseIdx i
          i := 0
        else
          i := i + 1
      else
        panic! "symbol ordering failed"

    return ordered

  namespace SymbolTable

    /--
    Generates a String representation of the ST.
    -/
    def toString (st : SymbolTable) : String :=
      s!"ST : \{
        blockName := {st.blockName},
        varDecls := {st.variableDecls},
        defDecls := {st.defDecls},
        axiomDecls := {st.axiomDecls},
        assertDecls := {st.assertDecls},
        requiredDecls := {st.requiredDecls}
      }"

    instance : ToString SymbolTable where
      toString := toString

    instance : Inhabited SymbolTable where
      default := {
        blockName := default,
        variableDecls := default,
        defDecls := default,
        axiomDecls := default,
        assertDecls := default,
        requiredDecls := default
      }

    /--
    Adds a single variable declaration to the ST
    -/
    def addVarDecl (st : SymbolTable) (vd : varDecl) : SymbolTable :=
      {st with
        variableDecls := st.variableDecls.append [vd]
      }

    /--
    Replaces the varDecls of the ST with the given ones
    -/
    def replaceVarDecls (st : SymbolTable) (vds : List (varDecl)) : SymbolTable :=
      {st with
        variableDecls := vds
      }

    /--
    Adds a single (Lean) definition declaration to the ST
    -/
    def addDefDecl (st : SymbolTable) (dd : commandDecl) : SymbolTable :=
      {st with
        defDecls := st.defDecls.concat dd
      }

    /--
    Adds a single (Lean) axiom declaration to the ST
    -/
    def addAxiomDecl (st : SymbolTable) (ad : commandDecl) : SymbolTable :=
      {st with
        axiomDecls := st.axiomDecls.concat ad
      }

    /--
    Adds a single (Lean) def declaration to the ST (cossosponding to an Assert)
    -/
    def addAssertDecl (st : SymbolTable) (ad : commandDecl) : SymbolTable :=
      {st with
        assertDecls := st.assertDecls.concat ad
      }

    /--
    Adds a single required declaration to the ST
    -/
    def addReqDecl (st : SymbolTable) (name : String) : SymbolTable :=
      {st with
        requiredDecls := st.requiredDecls.concat name
      }

    /--
    Adds multiple required declarations to the ST
    -/
    def addReqDecls (st : SymbolTable) (names : List (String)) : SymbolTable := Id.run do
      let mut temp : List (String) := []
      for name in names do
        temp := temp.concat name

      {st with
        requiredDecls := st.requiredDecls.append temp
      }

    def getAllFormulas (st : SymbolTable) : List (formula) :=
      ((
        (st.axiomDecls.map fun ad => ad.formulas) ++
        (st.defDecls.map fun dd => dd.formulas) ++
        (st.assertDecls.map fun ad => ad.formulas)
        ).join)

    /--
    Checks if all required symbols are present.

    This function stops at first error and states which symbol is missing.
    -/
    private def checkSymbols (st : SymbolTable) : Bool × String := Id.run do
      let availableSymbols : List (String) :=
        (st.variableDecls.map fun (vd) => vd.name) ++
          (st.axiomDecls.map  fun (ad) => ad.name) ++
            (st.defDecls.map  fun (dd) => dd.name) ++
            (st.defDecls.map  fun (dd) => (dd.args.map fun (arg) => arg.names).join).join

      for requiredSymbol in st.requiredDecls do
        if !(availableSymbols.contains requiredSymbol) then
          return (false, s!"{requiredSymbol} is not defined")

      return (true, "no error")

    /--
    Checks if all reffered Relations are not ambiguous

    This function stops at first error which symbol is ambiguous.
    -/
    private def checkRelationCalls (st : SymbolTable) : Bool × String := Id.run do
      let availableRelations : List (varDecl) :=
        st.variableDecls.filter fun (vd) => vd.isRelation

      let relationNames := availableRelations.map fun r => r.name

      let allFormulas := st.getAllFormulas

      let allRelationCalls :=
        (allFormulas.map
          fun f => f.getRelationCalls relationNames).join

      let allowedRelationCalls :=
        (allFormulas.map
          fun f => f.getQuantifiedRelationCalls relationNames).join

      let allowedRelationCallsString :=
        allowedRelationCalls.map fun arc => arc.1

      for rc in allRelationCalls do
        if !(allowedRelationCallsString.contains rc) then
          if !(rc.contains '.') then
            let possibleSignatures :=
              (availableRelations.filter
                fun vd => vd.name = rc).map
                  fun vd => s!"{vd.relationOf}"

            if (possibleSignatures.length > 1) then
            return (false,
              s!"{rc} is ambiguous. \
              It could refer to the relation \
              of the same name in the following \
              signatures {possibleSignatures}")

      return (true, "no error")

    /--
    Checks if the called signatures are valid and not ambiguous
    -/
    private def checkSignatureCalls
      (st : SymbolTable)
      : Bool × String := Id.run do

      let signatures := st.variableDecls.filter fun vd => !vd.isRelation

      let allCallLocations := st.assertDecls ++ st.axiomDecls ++ st.defDecls
      for location in allCallLocations do
        for signatureCall in location.signatureCalls do
          let possibleSignatures :=
            signatures.filter fun s => s.name == signatureCall

          if possibleSignatures.isEmpty then
            return (false, s!"No signature with name {signatureCall} is defined.")
          else
            if possibleSignatures.length > 1 then
              return (false, s!"The call to signature {signatureCall} is \
              ambiguous. It could refer so the signature of the blocks \
              {possibleSignatures.map
                fun ps => if ps.isOpened then ps.openedFrom else "this"}")

      return (true, "no error")

    /--
    Checks if all predicate calls are correct.

    Currently checks if the predicate exists and if the number of arguments are correct.

    TODO type checking of parameters

    This function stops at first error and states which symbol is missing.
    -/
    private def checkPredCalls
      (st : SymbolTable)
      (ast : AST)
      : Bool × String := Id.run do
        let availablePredDecls : List (predDecl) :=
          ast.predDecls

        let mut calledPreds : List (List (String)) :=
          ((st.axiomDecls.map fun (ad) => ad.predCalls).join ++
            ((st.defDecls.map fun (ad) => ad.predCalls).join) ++
              ((st.assertDecls.map fun (ad) => ad.predCalls).join))

        for cp in calledPreds do
          if !cp.isEmpty then
            let predName := cp.get! 0

            let pd? := availablePredDecls.find? fun (apd) => apd.name == predName
            if pd?.isNone then -- check: predicate exists?
              return (false, s!"Predicate {predName} does not exist")

            else -- check: number of arguments
              let pd := pd?.get!
              let args := pd.args
              let calledArgs := cp.drop 1

              let al := (args.map fun (elem) => elem.names).join.length
              let cal := calledArgs.length

              if al != cal then
                return (false,
                  s!"Definition {predName} called with {cal} arguments ({calledArgs}), but expected {al}")

        return (true, "no error")

    /--
    Adds the given signature declarations (including the contained signature field
    declarations) in the corosponding form (varDecl) to an existing (possibly emptyt) ST.

    Adding the signature declations also includes adding the corresponding requirements to the symbol table.
    -/
    private def addSigs
      (inputST : SymbolTable)
      (sigDecls : List (sigDecl))
      (moduleName : String := default)
      : SymbolTable := Id.run do

        let mut st : SymbolTable := inputST

        for sigDecl in sigDecls do

          -- ALL requirements for sigDecl
          let varRequirements :=
            sigDecl.extension.getReqVariables

          -- requirements for sigDecl (no duplicates)
          let localVarRequirements := varRequirements.eraseDups

          -- add all requirements for sigDecl to smybol table
          -- (if not already in symbol table)
          for requirement in localVarRequirements do
            if !(st.requiredDecls.contains requirement) then
              st := st.addReqDecl requirement

          -- add Declarations
          for signatureName in sigDecl.names do

            st := st.addVarDecl
                    ({  name:= signatureName,
                        isOpened := moduleName != default,
                        openedFrom := moduleName,
                        isRelation := false,
                        relationOf := default,
                        type := (sigDecl.extension.getType sigDecl.mult)
                        requiredDecls := localVarRequirements
                      } : varDecl)

            -- fields
            for field in sigDecl.fieldDecls do

              -- get complete Type from partial alloy type
              -- e.g. `sig A {r : some B}` is transformed
              -- to `r : A set → some B`
              let completeFieldType := match field.type with
                  | typeExpr.multExpr m e =>
                    typeExpr.arrowExpr
                      (arrowOp.multArrowOpExpr
                        (expr.string signatureName)
                        (mult.set) (m)
                        (e)
                      )

                  | typeExpr.relExpr e =>
                    typeExpr.arrowExpr
                      (arrowOp.multArrowOpExpr
                        (expr.string signatureName)
                        (mult.set) (mult.one)
                        (e)
                      )

                  | typeExpr.arrowExpr ae =>
                      typeExpr.arrowExpr
                        (arrowOp.multArrowOpExprLeft
                          (expr.string signatureName)
                          (mult.set)
                          (mult.set)
                          (ae)
                        )

              -- ALL requirements for Field
              let fieldRequirements := completeFieldType.getReqVariables

              -- requirements for sigDecl (no duplicates)
              let localFieldRequirements := fieldRequirements.eraseDups
--              let mut localFieldRequirements : List (String) := []


            -- add all requirements for fieldDecl to smybol table
            -- (if not already in symbol table)
              for requirement in localFieldRequirements do
                  if !(st.requiredDecls.contains requirement) then
                  st := st.addReqDecl requirement

              -- add fields
              for fieldName in field.names do

                st := st.addVarDecl ({
                      name:= fieldName,
                      isOpened := moduleName != default,
                      openedFrom := moduleName,
                      isRelation := true,
                      relationOf := signatureName,
                      type := completeFieldType,
                      requiredDecls := localFieldRequirements} : varDecl)

        return st

    /--
    Adds the given predicate declarations in the corosponding form (commandDecl) to the ST.

    (analogous to addSigs)
    -/
    private def addPreds
    (inputST : SymbolTable)
    (predDecls : List (predDecl))
    (moduleName : String := default)
    : SymbolTable := Id.run do

      let mut st := inputST

      let relationNames :=
        (st.variableDecls.filter
          fun vd => vd.isRelation).map
            fun vd => vd.name

      let signatureNames :=
        (st.variableDecls.filter
          fun vd => !vd.isRelation).map
            fun vd => vd.name

      for predDecl in predDecls do
        let mut predCalls : List (List (String)) := []
        let mut relCalls : List (String) := []
        let mut sigCalls : List (String) := []

        for formula in predDecl.forms do
          if let Option.some pc := formula.getPredCalls then
            predCalls := predCalls.concat pc

          let relationCalls := formula.getRelationCalls relationNames
          if !(relationCalls.isEmpty) then
            relCalls := relCalls.append relationCalls

          sigCalls :=
            sigCalls.append (formula.getSignatureCalls signatureNames)

        -- get list of referenced signatures and signature fields
        let reqVars : List (String) := predDecl.getReqVariables.eraseDups

        -- get list of referenced preds
        let reqDefs : List (String) := predDecl.getReqDefinitions.eraseDups

        let mut declarationName := predDecl.name
        /-
        if a moduleName is given, it is added to the
        signature name to make it unique
        -/
        if moduleName != default then
          declarationName :=
            s!"{moduleName}{signatureSeparator.get}{declarationName}"

        st := st.addDefDecl
          {   name := declarationName,
              args := predDecl.args,
              formulas := predDecl.forms,
              requiredVars := reqVars,
              requiredDefs := reqDefs,
              predCalls := predCalls,
              relationCalls := relCalls,
              signatureCalls := sigCalls
          }

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      return st

    /--
    Adds the given fact declarations in the corosponding form (commandDecl) to the ST

    (analogous to addSigs and addPreds)
    -/
    private def addFacts
    (inputST : SymbolTable)
    (factDecls : List (factDecl))
    (moduleName : String := default)
    : SymbolTable := Id.run do

      let mut st := inputST

      let relationNames :=
        (st.variableDecls.filter
          fun vd => vd.isRelation).map
            fun vd => vd.name

      let signatureNames :=
        (st.variableDecls.filter
          fun vd => !vd.isRelation).map
            fun vd => vd.name

      for factDecl in factDecls do
        let mut predCalls : List (List (String)):= []
        let mut relCalls : List (String) := []
        let mut sigCalls : List (String) := []

        -- get list of referenced preds (including arguments)
        for formula in factDecl.formulas do

          if let Option.some pc := formula.getPredCalls then
            predCalls := predCalls.concat pc

          let relationCalls := formula.getRelationCalls relationNames
          if !(relationCalls.isEmpty) then
            relCalls := relCalls.append relationCalls

          sigCalls :=
            sigCalls.append (formula.getSignatureCalls signatureNames)


        -- get list of the names of the referenced signatures and signature fields
        let reqVars : List (String) := factDecl.getReqVariables.eraseDups

        -- get list of the names of the referenced preds
        let reqDefs : List (String) := factDecl.getReqDefinitions.eraseDups

        let mut declarationName := factDecl.name
        /-
        if a moduleName is given, it is added to the
        signature name to make it unique
        -/
        if moduleName != default then
          declarationName :=
            s!"{moduleName}{signatureSeparator.get}{declarationName}"

        st := st.addAxiomDecl
          {   name := declarationName,
              args := [],
              formulas := factDecl.formulas,
              requiredVars := reqVars,
              requiredDefs := reqDefs,
              predCalls := predCalls,
              relationCalls := relCalls,
              signatureCalls := sigCalls
          }

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      return st

    /--
    Adds the given assert declarations in the corosponding form (commandDecl) to the ST

    (analogous to addSigs, addFacts and addPreds)
    -/
    private def addAsserts
    (inputST : SymbolTable)
    (assertDecls : List (assertDecl))
    (moduleName : String := default)
    : SymbolTable := Id.run do

      let mut st := inputST

      let relationNames :=
        (st.variableDecls.filter
          fun vd => vd.isRelation).map
            fun vd => vd.name

      let signatureNames :=
        (st.variableDecls.filter
          fun vd => !vd.isRelation).map
            fun vd => vd.name

      for assertDecla in assertDecls do
        let mut predCalls : List (List (String)):= []
        let mut relCalls : List (String) := []
        let mut signatureCalls : List (String) := []

        -- get list of referenced preds (including arguments)
        for formula in assertDecla.formulas do
          if let Option.some pc := formula.getPredCalls then
            predCalls := predCalls.concat pc

          let relationCalls := formula.getRelationCalls relationNames
          if !(relationCalls.isEmpty) then
            relCalls := relCalls.append relationCalls

          signatureCalls :=
            signatureCalls.append
              (formula.getSignatureCalls signatureNames)

        -- get list of the names of the referenced signatures and signature fields
        let reqVars : List (String) := assertDecla.getReqVariables.eraseDups

        -- get list of the names of the referenced preds
        let reqDefs : List (String) := assertDecla.getReqVariables.eraseDups

        let mut declarationName := assertDecla.name
        /-
        if a moduleName is given, it is added to the
        signature name to make it unique
        -/
        if moduleName != default then
          declarationName :=
            s!"{moduleName}{signatureSeparator.get}{declarationName}"

        st := st.addAssertDecl
          {   name := declarationName,
              args := [],
              formulas := assertDecla.formulas,
              requiredVars := reqVars,
              requiredDefs := reqDefs,
              predCalls := predCalls,
              relationCalls := relCalls,
              signatureCalls := signatureCalls
          }

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      return st

    private partial def addModule
      (input : SymbolTable)
      (ast : AST)
      : SymbolTable := Id.run do
        let mut st := input

        let mut name := ast.name
        /-
          dots (.) are not valid to be contained in
          the name a variable (in a typeclass), thus
          they are removed here
        -/
        if name.contains '.' then
          name := name.replace "." "_"

        /-
          add all sigs, preds, facts and asserts of the current MAIN module
        -/
        st := st.addSigs ast.sigDecls name
        st := st.addPreds ast.predDecls name
        st := st.addFacts ast.factDecls name
        st := st.addAsserts ast.assertDecls name

        /-
          if there are modules left, they have to be addes as well
        -/
        for module in ast.openedModules do
          st := st.addModule module

        return st


    /--
    Creates a SymbolTable from an AST
    -/
    def create (ast : AST) : SymbolTable × Bool × String := Id.run do
      let mut st : SymbolTable :=
        ({  blockName := ast.name,
            variableDecls := [],
            defDecls := [],
            axiomDecls := [],
            assertDecls := [],
            requiredDecls := []
          } : SymbolTable)

      -- Add elements from OPENED (imported) modules
      for openedModuleAST in ast.openedModules do
        st := st.addModule openedModuleAST

      -- Add the elements of the CURRENT module (block)
      -- sigs
      st := st.addSigs ast.sigDecls

      -- facts
      st := st.addFacts ast.factDecls

      --preds
      st := st.addPreds ast.predDecls

      --asserts
      st := st.addAsserts ast.assertDecls

      -- CHECKS
      let symbolCheck := st.checkSymbols
      if !symbolCheck.1 then
        return (st, false, symbolCheck.2)

      let relationCallCheck := st.checkRelationCalls
      if !relationCallCheck.1 then
        return (st, false, relationCallCheck.2)

      let sigCallCheck := st.checkSignatureCalls
      if !sigCallCheck.1 then
        return (st, false, sigCallCheck.2)

      let predCallCheck := st.checkPredCalls ast
      if !predCallCheck.1 then
        return (st, false, predCallCheck.2)

      -- Order the ST
      let orderedSt := (st.replaceVarDecls (orderVarDecls st.variableDecls))
      return (orderedSt, true, "no error")

  end SymbolTable

end Alloy
