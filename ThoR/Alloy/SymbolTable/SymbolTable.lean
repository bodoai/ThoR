/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
This file is used for semantic analysis of the AST and transforming its contents
to be better digestible for further computation and transformation into Lean.
-/

import ThoR.Alloy.SymbolTable.VarDecl.varDecl
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl
import ThoR.Shared.Syntax.Formula.formula

open Lean Shared

namespace Alloy

  /--
  A structure representation of the symbol table (ST).
  -/
  structure SymbolTable where
    mk :: (name : Name) -- name of the module
          (variableDecls : List (varDecl))
          (defDecls : List (commandDecl))
          (axiomDecls : List (commandDecl))
          (assertDecls : List (commandDecl))
          (requiredDecls : List (String))
  deriving Repr

  namespace SymbolTable

    /--
    Generates a String representation of the ST.
    -/
    def toString
      (st : SymbolTable)
      (inner_space_count := 3)
      (outer_space_count := 0)
      (leading_new_line := false)
      : String := Id.run do

      let mut inner_spaces : String := ""
      for _ in [0:inner_space_count] do
        inner_spaces := inner_spaces ++ " "

      let mut outer_spaces : String := ""
      for _ in [0:outer_space_count] do
        outer_spaces := outer_spaces ++ " "

      let variableDeclString :=
        st.variableDecls.map
          fun vd =>
            vd.toString
            (inner_space_count := (inner_space_count + 3))
            (outer_space_count := inner_space_count + 1)
            (leading_new_line := true)

      let defDeclsString :=
        st.defDecls.map
          fun vd =>
            vd.toString
            (inner_space_count := (inner_space_count + 3))
            (outer_space_count := inner_space_count + 1)
            (leading_new_line := true)

      let axiomDeclsString :=
        st.axiomDecls.map
          fun cd =>
            cd.toString
            (inner_space_count := (inner_space_count + 3))
            (outer_space_count := inner_space_count + 1)
            (leading_new_line := true)

      let assertDeclsString :=
        st.assertDecls.map
          fun cd =>
            cd.toString
            (inner_space_count := (inner_space_count + 3))
            (outer_space_count := inner_space_count + 1)
            (leading_new_line := true)

      let result :=
        outer_spaces ++ "symbol table : ⦃ \n" ++
        inner_spaces ++ s!"blockName := {st.name}," ++ "\n" ++
        inner_spaces ++ s!"varDecls := {variableDeclString}," ++ "\n" ++
        inner_spaces ++ s!"defDecls := {defDeclsString}," ++ "\n" ++
        inner_spaces ++ s!"axiomDecls := {axiomDeclsString}," ++ "\n" ++
        inner_spaces ++ s!"assertDecls := {assertDeclsString}," ++ "\n" ++
        inner_spaces ++ s!"requiredDecls := {st.requiredDecls}," ++ "\n" ++
        outer_spaces ++ "⦄"

      if leading_new_line then
        "\n" ++ result
      else
        result

    instance : ToString SymbolTable where
      toString := toString

    instance : Inhabited SymbolTable where
      default := {
        name := default,
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
    Updates the varDecls of the ST with the given ones
    -/
    def updateVarDecls (st : SymbolTable) (vds : List (varDecl)) : SymbolTable :=
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
    Updates the defDecls of the ST with the given ones
    -/
    def updateDefDecls
      (st : SymbolTable)
      (dds : List (commandDecl))
      : SymbolTable :=
        {st with defDecls := dds}

    /--
    Adds a single (Lean) axiom declaration to the ST
    -/
    def addAxiomDecl (st : SymbolTable) (ad : commandDecl) : SymbolTable :=
      {st with
        axiomDecls := st.axiomDecls.concat ad
      }

    /--
    Updates the axiomDecls of the ST with the given ones
    -/
    def updateAxiomDecls
      (st : SymbolTable)
      (ads : List (commandDecl))
      : SymbolTable :=
        {st with axiomDecls := ads}

    /--
    Adds a single (Lean) def declaration to the ST (cossosponding to an Assert)
    -/
    def addAssertDecl (st : SymbolTable) (ad : commandDecl) : SymbolTable :=
      {st with
        assertDecls := st.assertDecls.concat ad
      }

    /--
    Updates the assertDecls of the ST with the given ones
    -/
    def updateAssertDecls
      (st : SymbolTable)
      (ads : List (commandDecl))
      : SymbolTable :=
        {st with assertDecls := ads}

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

    def getPredicateDeclarations (st : SymbolTable) : List (commandDecl) :=
      (st.defDecls.filter fun cd => cd.isPredicate)

    def getFunctionDeclarations (st : SymbolTable) : List (commandDecl) :=
      (st.defDecls.filter fun cd => cd.isFunction)

    def updatePredicateDeclarations
      (st : SymbolTable)
      (newPredDecls : List (commandDecl))
      : SymbolTable :=
      let keepDecls := (st.defDecls.filter fun cd => !cd.isPredicate)
      {st with defDecls := (keepDecls ++ newPredDecls)}

    def updateFunctionDeclarations
      (st : SymbolTable)
      (newFunctionDecls : List (commandDecl))
      : SymbolTable :=
      let keepDecls := (st.defDecls.filter fun cd => !cd.isFunction)
      {st with defDecls := (keepDecls ++ newFunctionDecls)}

    end SymbolTable

end Alloy
