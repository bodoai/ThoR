/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
This file is used for semantic analysis of the AST and transforming its contents
to be better digestible for further computation and transformation into Lean.
-/

import ThoR.Alloy.SymbolTable.varDecl
import ThoR.Alloy.SymbolTable.commandDecl
import ThoR.Shared.Syntax.Formula.formula

open Lean Shared

namespace Alloy

  /--
  A structure representation of the symbol table (ST).
  -/
  structure SymbolTable where
    mk :: (name : String) -- name of the module
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
    def toString (st : SymbolTable) : String :=
      s!"ST : \{
        blockName := {st.name},
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

    def getPredicateDeclarations (st : SymbolTable) : List (commandDecl) :=
      (st.defDecls.filter fun cd => cd.isPredicate)

    end SymbolTable

end Alloy
