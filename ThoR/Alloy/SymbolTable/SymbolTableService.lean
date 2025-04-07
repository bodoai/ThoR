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
import ThoR.Alloy.SymbolTable.CommandDecl.commandDeclService
import ThoR.Alloy.Syntax.FactDecl.factDeclService
import ThoR.Alloy.Syntax.AssertDecl.assertDeclService

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
    private def checkSymbols
      (st : SymbolTable)
      (ast : AST)
      : Except String Unit := do
        let availableSymbols : List (String) :=
          (ast.modulVariables) ++
          (st.variableDecls.map fun (vd) => vd.name) ++
          (st.axiomDecls.map  fun (ad) => ad.name) ++
          (st.defDecls.map  fun (dd) => dd.name) ++
          (st.defDecls.map  fun (dd) =>
            (dd.predArgs.map fun (arg) => arg.1.names).join).join ++
          (st.defDecls.map  fun (dd) =>
            (dd.functionArgs.map fun (arg) => arg.1.names).join).join

        for requiredSymbol in st.requiredDecls do
          if !(availableSymbols.contains requiredSymbol) then
            throw s!"{requiredSymbol} is not defined in {availableSymbols}"

    /-
    The duplication of module names is checked here.
    This has the advantage that you only get an error if you use the
    faulty module.
    -/
    private def checkModuleImports (st : SymbolTable) : Except String Unit := do
      let importedVariableDeclarations :=
        st.variableDecls.filter fun vd => vd.isOpened

      if importedVariableDeclarations.isEmpty then return

      let importedModuleNames :=
        (importedVariableDeclarations.map fun vd => vd.openedFrom).eraseDups

      if importedModuleNames.isEmpty then return

      let alloyLikeModuleNames :=
        importedModuleNames.map fun name => (name.splitOn "_").getLastD name

      let mut lookedAtNames := []
      for index in [:(alloyLikeModuleNames.length)] do
        let alloyName := alloyLikeModuleNames.get! index
        let realName := importedModuleNames.get! index
        if lookedAtNames.contains alloyName then
          let indeces := alloyLikeModuleNames.indexesOf alloyName
          let doubleNamedModules := indeces.map fun i => importedModuleNames.get! i
          throw s!"Cannot import module '{realName}' \
          without alias (keyword 'as'), as the name '{alloyName}' \
          is ambiguous. Multiple modules end with {alloyName}: \
          ({doubleNamedModules})."

        lookedAtNames := lookedAtNames.concat alloyName

    /-- structure to encapsulate variableCalls -/
    private structure variableCalls where
      (relationCalls : List (String × List (varDecl)))
      (signatureCalls : List (String × List (varDecl)))

    /-- gets relation and signature calls of formulas -/
    private def get_relation_and_signature_calls_from_formulas
      (formulas : List (formula))
      (callableVariables : List (varDecl))
      : Except String variableCalls
        := do

      let mut calledVariables : List (String × List (varDecl)) := []
      for form in formulas do
          calledVariables :=
            calledVariables ++ (← form.getCalledVariables callableVariables)

      let calledRelations : List (String × List (varDecl)) :=
        calledVariables.map fun elem =>
          (elem.1, elem.2.filter fun elem => elem.isRelation)

      let calledSignatures : List (String × List (varDecl)) :=
        calledVariables.map fun elem =>
          (elem.1, elem.2.filter fun elem => !elem.isRelation)

      return {  relationCalls := calledRelations,
                signatureCalls := calledSignatures  }

    /-- gets relation and signature calls of expressions -/
    private def get_relation_and_signature_calls_from_expressions
      (expressions : List (expr))
      (callableVariables : List (varDecl))
      : Except String variableCalls
        := do

      let mut calledVariables : List (String × List (varDecl)) := []
      for expr in expressions do
          calledVariables :=
            calledVariables ++ (← expr.getCalledVariables callableVariables)

      let calledRelations : List (String × List (varDecl)) :=
        calledVariables.map fun elem =>
          (elem.1, elem.2.filter fun elem => elem.isRelation)

      let calledSignatures : List (String × List (varDecl)) :=
        calledVariables.map fun elem =>
          (elem.1, elem.2.filter fun elem => !elem.isRelation)

      return {  relationCalls := calledRelations,
                signatureCalls := calledSignatures  }

    private def checkRelationCalls
      (st : SymbolTable)
      : Except String Unit := do

        let variableCalls ←
          get_relation_and_signature_calls_from_formulas st.getAllFormulas st.variableDecls

        for relationCall in variableCalls.relationCalls do

          let calledName := relationCall.1
          let calledDecls := relationCall.2

          if calledDecls.isEmpty then
            continue

          if calledDecls.length > 1 then
            throw s!"The call to {calledName} is ambiguous. \
            Could be the relation from any of \
            {calledDecls.map fun c => s!"{c.openedFrom}/{c.relationOf}/{c.name}"}"

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

          let call := signatureCall.1
          let calledSigDecls := signatureCall.2

          if calledSigDecls.isEmpty then
            let index := location.signatureCalls.indexOf signatureCall
            let relCall := location.relationCalls.get! index
            let calledRelDecls := relCall.2

            if calledRelDecls.isEmpty then
              throw s!"The name {call} cannot be found. \
              (In {location.commandType}}
              {location.name})"
            continue

          if calledSigDecls.length > 1 then
            throw s!"The calls for signature {location.name} to \
            {call} are ambiguous. \
            Could be any of {signatureCall.2}"

          let calledSignature := signatureCall.2.get! 0

          -- temp quantors are not to be checked here
          if calledSignature.isQuantor then
            continue

          let possibleSignatures :=
            signatures.filter
              fun s =>
                s.name == calledSignature.name &&
                s.isOpened == calledSignature.isOpened &&
                s.openedFrom == calledSignature.openedFrom


          if possibleSignatures.isEmpty then
            throw s!"No signature with name {calledSignature.name} is defined."
          else
            if possibleSignatures.length > 1 then
              throw s!"The call to signature {signatureCall} is \
              ambiguous. It could refer so the signature of the blocks \
              {possibleSignatures.map
                fun ps => ps.openedFrom}"

    /--
    Check if the number of arguments match
    -/
    private def checkPredCallArgNumber
      (calledPredDecl : predDecl)
      (calledArguments : List (expr × List (String × List varDecl)))
      : Except String Unit := do
        let requiredArgNumber :=
          (calledPredDecl.args.map fun a => a.names).join.length

        let calledArgNumber := calledArguments.length

        let isCorrectNumberOfArguments := requiredArgNumber == calledArgNumber
        if !isCorrectNumberOfArguments then
          throw s!"Definition {calledPredDecl.name} called with {calledArgNumber} \
          arguments ({calledArguments}), but expected {requiredArgNumber} arguments"

    /--
    Checks if all predicate calls are correct.

    Currently checks if the predicate exists and if the number of arguments are correct.

    TODO: type checking of parameters
    -/
    private def checkPredCalls
      (st : SymbolTable)
      (ast : AST)
      : Except String Unit := do
        let availablePredDecls : List (predDecl) :=
          ast.predDecls

        let availablePredNames := availablePredDecls.map fun apd => apd.name

        let mut calledPreds :=
          ((st.axiomDecls.map fun (ad) => ad.predCalls).join ++
            ((st.defDecls.map fun (ad) => ad.predCalls).join) ++
              ((st.assertDecls.map fun (ad) => ad.predCalls).join))

        for calledPred in calledPreds do
          let calledPredCommandDecl := calledPred.1
          let calledPredName := calledPredCommandDecl.name

          let isDefined := availablePredNames.contains calledPredName
          if !isDefined then
            throw s!"Predicate {calledPredName} does not exist"

          let index := availablePredNames.indexOf calledPredName

          let calledPredDecl := availablePredDecls.get! index
          let calledArguments := calledPred.2

          checkPredCallArgNumber calledPredDecl calledArguments

    /--
    If possible replace domain restrictions with relations.

    This is only possible, if the relation is restricted from the
    signature it is defined in.

    E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
    -/
    private def simplifyDomainRestrictions
      (input : SymbolTable)
      : SymbolTable := Id.run do

      let mut st := input

      -- simplify the varDecls
      st :=
        st.updateVarDecls
          (st.variableDecls.map fun vd =>
            vd.simplifyDomainRestrictions st)

      st :=
        st.updateDefDecls
          (st.defDecls.map fun dd =>
            dd.simplifyDomainRestrictions st)

      st :=
        st.updateAxiomDecls
          (st.axiomDecls.map fun ad =>
            ad.simplifyDomainRestrictions st)

      st :=
        st.updateAssertDecls
          (st.assertDecls.map fun ad =>
            ad.simplifyDomainRestrictions st)

      return st

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
    : Except String SymbolTable := do

      let mut st := inputST

      for predDecl in predDecls do

        -- first simplyfiy the domain restrictions
        let mut predDecl := predDecl.simplifyDomainRestrictions st

        if moduleName != default then
          predDecl := predDecl.replaceThisCalls moduleName

        -- get list of referenced signatures and signature fields
        let reqVars : List (String) := predDecl.getReqVariables.eraseDups

        -- get list of referenced preds
        let reqDefs : List (String) := predDecl.getReqDefinitions.eraseDups

        -- get relation and signature calls
        let variableCalls ←
          get_relation_and_signature_calls_from_formulas predDecl.forms st.variableDecls

        let mut declarationName := predDecl.name
        /-
        if a moduleName is given, it is added to the
        name to make it unique
        -/
        if moduleName != default then
          declarationName :=
            s!"{moduleName}{signatureSeparator}{declarationName}"

        let newArgs := predDecl.args.map fun a =>
          if !a.expression.isString then
            (a, default)
          else
            let fv := (st.variableDecls.filter
              fun cv =>
                cv.name == a.expression.getStringData).get! 0
            (a, fv)

        let functionCalls ←
          predDecl.getFunctionCalls st.getFunctionDeclarations st.variableDecls

        st := st.addDefDecl
          (
            commandDecl.mk (name := declarationName)
            (predArgs := newArgs)
            (commandType := commandType.pred)
            (formulas := predDecl.forms)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := [])
            (functionCalls := functionCalls)
            (relationCalls := variableCalls.relationCalls)
            (signatureCalls := variableCalls.signatureCalls)
          )

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      -- add calls to preds only after all preds are defined
      let mut newPredDefDecls := []
      for predDefDecl in st.getPredicateDeclarations do
        let mut predicateCalls := []
        for form in predDefDecl.formulas do
          predicateCalls :=
            predicateCalls ++
            (← form.getCalledPredicates st.getPredicateDeclarations st.variableDecls)

        let newPredDefDecl :=
          commandDecl.mk
            (name := predDefDecl.name)
            (commandType := predDefDecl.commandType)
            (predArgs := predDefDecl.predArgs)
            (formulas := predDefDecl.formulas)
            (requiredVars := predDefDecl.requiredVars)
            (requiredDefs := predDefDecl.requiredDefs)
            (predCalls := predicateCalls)
            (functionCalls := predDefDecl.functionCalls)
            (relationCalls := predDefDecl.relationCalls)
            (signatureCalls := predDefDecl.signatureCalls)

        newPredDefDecls := newPredDefDecls.concat newPredDefDecl

      return st.updatePredicateDeclarations newPredDefDecls

    /--
    Adds the given fact declarations in the corosponding form (commandDecl) to the ST

    (analogous to addSigs and addPreds)
    -/
    private def addFacts
    (inputST : SymbolTable)
    (factDecls : List (factDecl))
    (moduleName : String := default)
    : Except String SymbolTable := do

      let mut st := inputST

      for factDecl in factDecls do

        let mut factDecl := factDecl.simplifyDomainRestrictions st

        if moduleName != default then
          factDecl := factDecl.replaceThisCalls moduleName

        let mut predicateCalls := []
        for form in factDecl.formulas do
          predicateCalls :=
            predicateCalls ++
            (← form.getCalledPredicates
                st.getPredicateDeclarations
                st.variableDecls)

        let functionCalls ←
          factDecl.getFunctionCalls st.getFunctionDeclarations st.variableDecls

        -- get relation and signature calls
        let variableCalls ←
          get_relation_and_signature_calls_from_formulas factDecl.formulas st.variableDecls

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
            (commandType := commandType.fact)
            (formulas := factDecl.formulas)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := predicateCalls)
            (functionCalls := functionCalls)
            (relationCalls := variableCalls.relationCalls)
            (signatureCalls := variableCalls.signatureCalls)
          )

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      return st

    /--
    Adds the given function declarations in the corosponding form (commandDecl) to the ST
    -/
    private def addFunctions
    (inputST : SymbolTable)
    (functionDecls : List (functionDecl))
    (moduleName : String := default)
    : Except String SymbolTable := do

      let mut st := inputST

      for functionDecl in functionDecls do

        let mut functionDecl := functionDecl.simplifyDomainRestrictions st

        if moduleName != default then
          functionDecl := functionDecl.replaceThisCalls moduleName

        -- get relation and signature calls
        let variableCalls ←
          get_relation_and_signature_calls_from_expressions functionDecl.expressions st.variableDecls

        -- get list of the names of the referenced signatures and signature fields
        let reqVars : List (String) := functionDecl.getReqVariables.eraseDups

        let mut declarationName := functionDecl.name
        /-
        if a moduleName is given, it is added to the
        signature name to make it unique
        -/
        if moduleName != default then
          declarationName :=
            s!"{moduleName}{signatureSeparator}{declarationName}"

        let newArgs := functionDecl.arguments.map fun a =>
          if !a.type.isString then
            (a, default)
          else
            let fv := (st.variableDecls.filter
              fun cv =>
                cv.name == a.type.getStringData).get! 0
            (a, fv)

        st := st.addDefDecl
          (
            commandDecl.mk
            (name := declarationName)
            (commandType := commandType.function)
            (functionArgs := newArgs)
            (functionReturnType := functionDecl.outputType)
            (expressions := functionDecl.expressions)
            (ifExpressions := functionDecl.ifExpressions)
            (requiredVars := reqVars)
            (requiredDefs := default)
            (predCalls := default)
            (functionCalls := [])
            (relationCalls := variableCalls.relationCalls)
            (signatureCalls := variableCalls.signatureCalls)
          )

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars))
          }

      -- add calls to functions only after all functions are defined
      let mut newFunctionDefDecls := []
      for functionDefDecl in st.getFunctionDeclarations do
        let mut functionCalls := []
        for expr in functionDefDecl.expressions do
          functionCalls :=
            functionCalls ++
            (← expr.getFunctionCalls st.defDecls st.variableDecls)

        let newFunctionDefDecl :=
          commandDecl.mk
            (name := functionDefDecl.name)
            (commandType := functionDefDecl.commandType)
            (predArgs := functionDefDecl.predArgs)
            (formulas := functionDefDecl.formulas)
            (requiredVars := functionDefDecl.requiredVars)
            (requiredDefs := functionDefDecl.requiredDefs)
            (predCalls := functionDefDecl.predCalls)
            (functionCalls := functionCalls)
            (relationCalls := functionDefDecl.relationCalls)
            (signatureCalls := functionDefDecl.signatureCalls)

        newFunctionDefDecls := newFunctionDefDecls.concat newFunctionDefDecl

      return st.updateFunctionDeclarations newFunctionDefDecls

    /--
    Adds the given assert declarations in the corosponding form (commandDecl) to the ST

    (analogous to addSigs, addFacts and addPreds)
    -/
    private def addAsserts
    (inputST : SymbolTable)
    (assertDecls : List (assertDecl))
    (moduleName : String := default)
    : Except String SymbolTable := do

      let mut st := inputST

      for assertDecla in assertDecls do

        let mut assertDecla := assertDecla.simplifyDomainRestrictions st

        if moduleName != default then
          assertDecla := assertDecla.replaceThisCalls moduleName

        let mut predicateCalls := []
        for form in assertDecla.formulas do
          predicateCalls :=
            predicateCalls ++
            (← form.getCalledPredicates
                st.getPredicateDeclarations
                st.variableDecls)

         -- get relation and signature calls
        let variableCalls ←
          get_relation_and_signature_calls_from_formulas assertDecla.formulas st.variableDecls

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

        let functionCalls ←
          assertDecla.getFunctionCalls st.getFunctionDeclarations st.variableDecls

        st := st.addAssertDecl
          (
            commandDecl.mk
            (name := declarationName)
            (commandType := commandType.assert)
            (formulas := assertDecla.formulas)
            (requiredVars := reqVars)
            (requiredDefs := reqDefs)
            (predCalls := predicateCalls)
            (functionCalls := functionCalls)
            (relationCalls := variableCalls.relationCalls)
            (signatureCalls := variableCalls.signatureCalls)
          )

        st :=
          {st with requiredDecls
            := List.eraseDups (st.requiredDecls ++ (reqVars ++ reqDefs))
          }

      return st

    private def addElements
      (input : SymbolTable)
      (ast : AST)
      (module_name : String := default)
      : Except String SymbolTable := do
        let mut st := input
        if module_name == default then
          st := st.addSigs ast.sigDecls
          st ← st.addFunctions ast.functionDecls
          st ← st.addPreds ast.predDecls
          st ←  st.addFacts ast.factDecls
          st ←  st.addAsserts ast.assertDecls
        else
          st := st.addSigs ast.sigDecls module_name
          st ← st.addFunctions ast.functionDecls module_name
          st ← st.addPreds ast.predDecls module_name
          st ←  st.addFacts ast.factDecls module_name
          st ←  st.addAsserts ast.assertDecls module_name
        return st

    private partial def addModule
      (input : SymbolTable)
      (ast : AST)
      : Except String SymbolTable := do
        let mut st := input

        let mut module_name := ast.name.toString
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
        st ← st.addElements ast module_name

        /-
          if there are modules left, they have to be addes as well
        -/
        for module in ast.openedModules do
          st ← st.addModule module

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
          ({  name := ast.name,
              variableDecls := [],
              defDecls := [],
              axiomDecls := [],
              assertDecls := [],
              requiredDecls := []
            } : SymbolTable)

        -- Add elements from OPENED (imported) modules
        for openedModuleAST in ast.openedModules do
          st ←  st.addModule openedModuleAST

        -- Add the elements of the CURRENT module (block)
        st ← st.addElements ast

        -- CHECKS
        if let Except.error msg := st.checkSymbols ast then
          if extensive_logging then
            throw (getExtensiveErrorMsg msg st)
          else
            throw msg

        if let Except.error msg := st.checkModuleImports then
          if extensive_logging then
            throw (getExtensiveErrorMsg msg st)
          else
            throw msg

        if let Except.error msg := st.checkModuleImports then
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
        return (st.updateVarDecls (orderVarDecls st.variableDecls))

  end Alloy.SymbolTable
