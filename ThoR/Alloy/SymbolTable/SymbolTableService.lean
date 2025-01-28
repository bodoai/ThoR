/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Relation
import ThoR.Alloy.Syntax.AST
import ThoR.Alloy.Config
import ThoR.Alloy.SymbolTable.SymbolTable

open Shared Config

/-
This file is used for semantic analysis of the AST and transforming its contents
to be better digestible for further computation and transformation into Lean.
-/


  namespace Alloy.SymbolTable

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
              fun s =>
                s.name == signatureCall.name &&
                s.isOpened == signatureCall.isOpened &&
                s.openedFrom == signatureCall.openedFrom


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

        let calledVariables : List (varDecl) :=
          (predDecl.forms.map fun f => f.getCalledVariables st.variableDecls).join

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
            (isPredicate := true)
            (formulas := predDecl.forms)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := [])
            (relationCalls := calledVariables.filter fun cv => cv.isRelation)
            (signatureCalls := calledVariables.filter fun cv => !cv.isRelation)
          )

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      -- add calls to preds only after all preds are defined
      let mut newPredDefDecls := []
      for predDefDecl in st.defDecls do
        let predicateCalls :=
          (predDefDecl.formulas.map
            fun f => f.getCalledPredicates st.defDecls st.variableDecls).join

        let newPredDefDecl :=
          commandDecl.mk
            (name := predDefDecl.name)
            (isPredicate := predDefDecl.isPredicate)
            (args := predDefDecl.args)
            (formulas := predDefDecl.formulas)
            (requiredVars := predDefDecl.requiredVars)
            (requiredDefs := predDefDecl.requiredDefs)
            (predCalls := predicateCalls)
            (relationCalls := predDefDecl.relationCalls)
            (signatureCalls := predDefDecl.signatureCalls)

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

        let predicateCalls :=
          (factDecl.formulas.map
            fun f =>
              f.getCalledPredicates
                st.getPredicateDeclarations
                st.variableDecls
          ).join

        let variableCalls :=
          (factDecl.formulas.map
            fun f =>
              f.getCalledVariables
                st.variableDecls
          ).join

        let relationCalls := variableCalls.filter fun vc => vc.isRelation
        let signatureCalls := variableCalls.filter fun vc => !vc.isRelation

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
            (predCalls := predicateCalls)
            (relationCalls := relationCalls)
            (signatureCalls := signatureCalls)
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

        let predicateCalls :=
          (assertDecla.formulas.map
            fun f =>
              f.getCalledPredicates
                st.getPredicateDeclarations
                st.variableDecls
          ).join

        let variableCalls :=
          (assertDecla.formulas.map
            fun f =>
              f.getCalledVariables
                st.variableDecls
          ).join

        let relationCalls := variableCalls.filter fun vc => vc.isRelation
        let signatureCalls := variableCalls.filter fun vc => !vc.isRelation

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
            (predCalls := predicateCalls)
            (relationCalls := relationCalls)
            (signatureCalls := signatureCalls)
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

  end Alloy.SymbolTable
