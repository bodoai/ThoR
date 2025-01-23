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
import ThoR.Alloy.Config

open Lean
open Shared Config

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
        requiredDecls := {st.requiredDecls},
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
    Get all defined relations (signature fields) from the symbol table
    -/
    def getRelations (st : SymbolTable) : List (varDecl) :=
      st.variableDecls.filter fun vd => vd.isRelation

    /--
    Get all defined signatures from the symbol table
    -/
    def getSignatures (st : SymbolTable) : List (varDecl) :=
      st.variableDecls.filter fun vd => !vd.isRelation

    /--
    Get all signature names from the symbol table
    -/
    def getSignatureNames (st : SymbolTable) : List (String) :=
      (st.variableDecls.filter fun vd => !vd.isRelation).map
        fun s => s.name

    /--
    Get all replacement signature names from the symbol table.
    -/
    def getSignatureRNames (st : SymbolTable) : List (String) :=
      (st.variableDecls.filter fun vd => !vd.isRelation).map
        fun s => s.getSignatureReplacementName

    /--
    Checks if all required symbols are present.

    This function stops at first error and states which symbol is missing.
    -/
    private def checkSymbols (st : SymbolTable) : Except String Unit := do
      let availableSymbols : List (String) :=
        (st.variableDecls.map fun (vd) => vd.name) ++
          (st.axiomDecls.map  fun (ad) => ad.name) ++
            (st.defDecls.map  fun (dd) => dd.name) ++
            (st.defDecls.map  fun (dd) => (dd.args.map fun (arg) => arg.names).join).join

      for requiredSymbol in st.requiredDecls do
        if !(availableSymbols.contains requiredSymbol) then
          throw s!"{requiredSymbol} is not defined"

    /--
    Checks if all reffered Relations are not ambiguous

    This function stops at first error which symbol is ambiguous.
    -/
    private def checkRelationCalls
      (st : SymbolTable)
      : Except String Unit := do
        let availableRelations : List (varDecl) :=
          st.variableDecls.filter fun (vd) => vd.isRelation

        let relationNames := availableRelations.map fun r => r.name

        let allFormulas := st.getAllFormulas

        let allRelationCalls :=
          (allFormulas.map
            fun f => f.getRelationCalls relationNames).join

        let allowedQuantifiedRelationCalls :=
          (allFormulas.map
            fun f => f.getQuantifiedRelationCalls relationNames).join

        let allowedQuantifiedRelationCallsStrings :=
          allowedQuantifiedRelationCalls.map fun arc => arc.1

        for rc in allRelationCalls do
          -- is in quantification or not
          if !(allowedQuantifiedRelationCallsStrings.contains rc) then
            if !(rc.contains '.') then
              let possibleSignatures :=
                (availableRelations.filter
                  fun vd => vd.name = rc).map
                    fun vd => s!"{vd.relationOf}"

              if (possibleSignatures.length > 1) then
                throw s!"{rc} is ambiguous. \
                      It could refer to the relation \
                      of the same name in the following \
                      signatures {possibleSignatures}"

            else
              let rcSplit := rc.splitOn "."
              if rcSplit.isEmpty then
                throw s!"No relation for {rc} found"
              else
                let lastSplit := rcSplit.getLast!

                let complete_origin : String :=
                  ((rcSplit.drop 1).reverse.drop 1).reverse.foldl
                    (fun string split => s!"{string}_{split}")
                    (rcSplit.get! 0)

                let possibleSigName :=
                  if rcSplit.length > 1 then
                    rcSplit.get! (rcSplit.length - 2)
                  else
                    rcSplit.getLast!

                let origin_without_sig :=
                  complete_origin.replace s!"_{possibleSigName}" ""

                let possibleRelations :=
                  (availableRelations.filter
                    fun ar => (ar.name == lastSplit &&
                      (ar.openedFrom == complete_origin ||
                        (possibleSigName == ar.relationOf &&
                          ar.openedFrom == origin_without_sig
                        ) ||
                        (origin_without_sig == possibleSigName)
                      )

                      ))

                if possibleRelations.isEmpty then
                  throw s!"No Relation {lastSplit} found \
                  in module {complete_origin} or \
                  under signature {possibleSigName} \
                  in {origin_without_sig}}]"

    /--
    Checks if the called signatures are valid and not ambiguous
    -/
    private def checkSignatureCalls
      (st : SymbolTable)
      : Except String Unit := do

      let signatures := st.variableDecls.filter fun vd => !vd.isRelation

      let allCallLocations := st.assertDecls ++ st.axiomDecls ++ st.defDecls
      for location in allCallLocations do
        for signatureCall in location.signatureCalls do

          -- temp quantors are not to be checked here
          if signatureCall.isQuantor then
            continue

          let possibleSignatures :=
            signatures.filter
              fun s => s.name == signatureCall.name

          if possibleSignatures.isEmpty then
            throw s!"No signature with name {signatureCall.name} is defined."
          else
            if possibleSignatures.length > 1 then
              throw s!"The call to signature {signatureCall} is \
              ambiguous. It could refer so the signature of the blocks \
              {possibleSignatures.map
                fun ps => ps.openedFrom}"

    /--
    Checks if all predicate calls are correct.

    Currently checks if the predicate exists and if the number of arguments are correct.

    TODO type checking of parameters

    This function stops at first error and states which symbol is missing.
    -/
    private def checkPredCalls
      (st : SymbolTable)
      (ast : AST)
      : Except String Unit := do
        let availablePredDecls : List (predDecl) :=
          ast.predDecls

        let avariablePredDeclNames := availablePredDecls.map fun apd => apd.name

        let mut calledPreds :=
          ((st.axiomDecls.map fun (ad) => ad.predCalls).join ++
            ((st.defDecls.map fun (ad) => ad.predCalls).join) ++
              ((st.assertDecls.map fun (ad) => ad.predCalls).join))

        for cp in calledPreds do
          let calledName := cp.1.name
          let isDefined := avariablePredDeclNames.contains calledName
          if !isDefined then
            throw s!"Predicate {calledName} does not exist"

          let index := avariablePredDeclNames.indexOf calledName
          let calledPredDecl := availablePredDecls.get! index
          let calledArguments := cp.2
          let requiredArgNumber :=
            (calledPredDecl.args.map fun a => a.names).join.length
          let calledArgNumber := calledArguments.length

          let isCorrectNumberOfArguments := requiredArgNumber == calledArgNumber
          if !isCorrectNumberOfArguments then
            throw s!"Definition {calledName} called with {calledArgNumber} \
            arguments ({calledArguments}), but expected {requiredArgNumber} arguments"

    /--
    Adds the given signature declarations (including the contained signature field
    declarations) in the corosponding form (varDecl) to an existing (possibly emptyt) ST.

    Adding the signature declations also includes adding the corresponding requirements to the symbol table.
    -/
    private def addSigs
      (inputST : SymbolTable)
      (sigDecls : List (sigDecl))
      (moduleName : String := "this")
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
                        isOpened := moduleName != "this",
                        openedFrom := moduleName,
                        isRelation := false,
                        relationOf := default,
                        isQuantor := false,
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

            -- add all requirements for fieldDecl to smybol table
            -- (if not already in symbol table)
              for requirement in localFieldRequirements do
                  if !(st.requiredDecls.contains requirement) then
                  st := st.addReqDecl requirement

              -- add fields
              for fieldName in field.names do

                st := st.addVarDecl ({
                      name:= fieldName,
                      isOpened := moduleName != "this",
                      openedFrom := moduleName,
                      isRelation := true,
                      relationOf := signatureName,
                      isQuantor := false,
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

      for predDecl in predDecls do
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
            s!"{moduleName}{signatureSeparator}{declarationName}"

        st := st.addDefDecl
          (
            commandDecl.mk (name := declarationName)
            (args := predDecl.args)
            (formulas := predDecl.forms)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := [])
            (relationCalls := [])
            (signatureCalls := [])
          )

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      -- add calls to preds only after all preds are defined
      let mut newPredDefDecls := []
      for predDefDecl in st.defDecls do
        let calls :=
          predDefDecl.formulas.map
            fun f =>
              f.getCalls st.variableDecls st.defDecls

        let mut allVarCalls := []
        let mut allPredCals := []
        for call in calls do
          allVarCalls := allVarCalls.append call.1
          allPredCals := allPredCals.append call.2

        let newPredDefDecl :=
          commandDecl.mk
            (name := predDefDecl.name)
            (args := predDefDecl.args)
            (formulas := predDefDecl.formulas)
            (requiredVars := predDefDecl.requiredVars)
            (requiredDefs := predDefDecl.requiredDefs)
            (predCalls := allPredCals)
            (relationCalls := allVarCalls.filter fun vc => vc.isRelation)
            (signatureCalls := allVarCalls.filter fun vc => !vc.isRelation)

        newPredDefDecls := newPredDefDecls.concat newPredDefDecl

      return {st with defDecls := newPredDefDecls}

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

      for factDecl in factDecls do

        let mut predCalls := []
        let mut relCalls := []
        let mut sigCalls := []

        -- get list of referenced preds (including arguments)
        for formula in factDecl.formulas do

          let calls := formula.getCalls st.variableDecls st.defDecls

          predCalls := predCalls.append
            calls.2

          relCalls := relCalls.append
            (calls.1.filter fun c => c.isRelation)

          sigCalls :=
            (calls.1.filter fun c => !c.isRelation)


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
            s!"{moduleName}{signatureSeparator}{declarationName}"

        st := st.addAxiomDecl
          (
            commandDecl.mk
            (name := declarationName)
            (args := [])
            (formulas := factDecl.formulas)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := predCalls)
            (relationCalls := relCalls)
            (signatureCalls := sigCalls)
          )

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

      for assertDecla in assertDecls do
        let mut predCalls := []
        let mut relCalls := []
        let mut sigCalls := []

        -- get list of referenced preds (including arguments)
        for formula in assertDecla.formulas do

          let calls := formula.getCalls st.variableDecls st.defDecls

          predCalls := predCalls.append
            calls.2

          relCalls := relCalls.append
            (calls.1.filter fun c => c.isRelation)

          sigCalls :=
            (calls.1.filter fun c => !c.isRelation)

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
            s!"{moduleName}{signatureSeparator}{declarationName}"

        st := st.addAssertDecl
          (
            commandDecl.mk
            (name := declarationName)
            (args := [])
            (formulas := assertDecla.formulas)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := predCalls)
            (relationCalls := relCalls)
            (signatureCalls := sigCalls)
          )

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

        let mut module_name := ast.name
        /-
          dots (.) are not valid to be contained in
          the name of a variable (in a typeclass), thus
          they are removed here
        -/
        if module_name.contains '.' then
          module_name := module_name.replace "." "_"

        /-
          add all sigs, preds, facts and asserts of the current MAIN module
        -/
        st := st.addSigs ast.sigDecls module_name
        st := st.addPreds ast.predDecls module_name
        st := st.addFacts ast.factDecls module_name
        st := st.addAsserts ast.assertDecls module_name

        /-
          if there are modules left, they have to be addes as well
        -/
        for module in ast.openedModules do
          st := st.addModule module

        return st

    private def getExtensiveErrorMsg
      (msg : String)
      (st : SymbolTable)
      : String := s!"Error: '{msg}' occured in \n\n {st}"

    /--
    Creates a SymbolTable from an AST
    -/
    def create
      (ast : AST)
      (extensive_logging : Bool := false)
      : Except String SymbolTable := do
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
        if let Except.error msg := st.checkSymbols then
          if extensive_logging then
            throw (getExtensiveErrorMsg msg st)
          else
            throw msg

        if let Except.error msg := st.checkRelationCalls then
          if extensive_logging then
            throw (getExtensiveErrorMsg msg st)
          else
            throw msg

        if let Except.error msg := st.checkSignatureCalls then
          if extensive_logging then
            throw (getExtensiveErrorMsg msg st)
          else
            throw msg

        if let Except.error msg := st.checkPredCalls ast then
          if extensive_logging then
            throw (getExtensiveErrorMsg msg st)
          else
            throw msg

        -- Order the ST
        return (st.replaceVarDecls (orderVarDecls st.variableDecls))

  end SymbolTable

end Alloy
