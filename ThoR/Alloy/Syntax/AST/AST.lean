/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
This file is used to parse and precompile the alloy syntax.
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.Signature
import ThoR.Alloy.Syntax.FactDecl.factDecl
import ThoR.Alloy.Syntax.AssertDecl.assertDecl
import ThoR.Alloy.Syntax.Function.FunctionDecl.functionDecl
import ThoR.Alloy.Syntax.specification

open Lean
open Shared

namespace Alloy

/--
A structure representation of the abstract syntax tree (AST) of Alloy.
-/
inductive AST
  | mk  (name : Name)
        (modulVariables : List (String))
        (sigDecls : List (sigDecl))
        (functionDecls : List (functionDecl))
        (factDecls : List (factDecl))
        (assertDecls : List (assertDecl))
        (predDecls : List (predDecl))
        (modulesToOpen : List (openModule))
        (openedModules : List (AST))
deriving Repr

  namespace AST

    def name | mk name _ _ _ _ _ _ _ _ => name
    def modulVariables | mk _ modulVariables _ _ _ _ _ _ _ => modulVariables
    def sigDecls | mk _ _ sigDecls _ _ _ _ _ _ => sigDecls
    def functionDecls | mk _ _ _ functionDecls _ _ _ _ _ => functionDecls
    def factDecls | mk _ _ _ _ factDecls _ _ _ _ => factDecls
    def assertDecls | mk _ _ _ _ _ assertDecls _ _ _ => assertDecls
    def predDecls | mk _ _ _ _ _ _ predDecls _ _ => predDecls
    def modulesToOpen | mk _ _ _ _ _ _ _ modulesToOpen _ => modulesToOpen
    def openedModules | mk _ _ _ _ _ _ _ _ openedModules => openedModules

    instance : Inhabited AST where
      default :=
        AST.mk
          (name := default)
          (modulVariables := default)
          (sigDecls := default)
          (functionDecls := default)
          (factDecls := default)
          (assertDecls := default)
          (predDecls := default)
          (modulesToOpen := default)
          (openedModules := default)

    /--
    Generates a String representation of the AST
    -/
    partial def toString (ast : AST) : String := Id.run do
      let oms := ast.openedModules.map fun om => toString om

      s!"AST : \{
          name := {ast.name},
          sigDecls := {ast.sigDecls},
          factDecls := {ast.factDecls},
          functionDecls := {ast.functionDecls},
          assertDecls := {ast.assertDecls},
          predDecls := {ast.predDecls},
          modules to open := {ast.modulesToOpen},
          opened modules := {oms}
        }"

    instance : ToString AST where
    toString ( ast : AST ) : String := toString ast

    /--
    Updates the name of the AST to the given value
    -/
    def updateName (name : Name)
      | mk _ modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Updates the moduleVariables of the AST to the given value
    -/
    def updateModuleVariables (modulVariables : List (String))
      | mk name _ sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Updates the sigDecls of the AST to the given value
    -/
    def updateSigDecls (sigDecls : List (sigDecl))
      | mk name modulVariables _ functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Updates the functionDecls of the AST to the given value
    -/
    def updateFunctionDecls (functionDecls : List (functionDecl))
      | mk name modulVariables sigDecls _ factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Updates the factDecls of the AST to the given value
    -/
    def updateFactDecls (factDecls : List (factDecl))
      | mk name modulVariables sigDecls functionDecls _ assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Updates the factDecls of the AST to the given value
    -/
    def updateAssertDecls (assertDecls : List (assertDecl))
      | mk name modulVariables sigDecls functionDecls factDecls _
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Updates the factDecls of the AST to the given value
    -/
    def updatePredDecls (predDecls : List (predDecl))
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        _ modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls modulesToOpen openendModules

    /--
    Clears the modules to open from the AST
    -/
    def clearModulesToOpen
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls _ openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls default openendModules

    /--
    Clears the moduleVariables from the AST
    -/
    def clearModuleVariables
      |  mk name _ sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name default sigDecls functionDecls factDecls assertDecls
          predDecls modulesToOpen openendModules

    /--
    Adds a single `sigDecl` to the AST
    -/
    def addSigDecl (sd : sigDecl)
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables (sigDecls.concat sd) functionDecls
          factDecls assertDecls predDecls modulesToOpen openendModules

    /--
    Adds a single `functionDecl` to the AST
    -/
    def addFunctionDecl (fd : functionDecl)
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls (functionDecls.concat fd)
          factDecls assertDecls predDecls modulesToOpen openendModules

    /--
    Adds a single `factDecl` to the AST
    -/
    def addFactDecl (fd : factDecl)
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls
          (factDecls.concat fd) assertDecls predDecls modulesToOpen
          openendModules

    /--
    Adds a single `assertDecl` to the AST
    -/
    def addAssertDecl (ad : assertDecl)
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          (assertDecls.concat ad) predDecls modulesToOpen openendModules

    /--
    Adds a single `predDecl` to the AST
    -/
    def addPredDecl (pd : predDecl)
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls (predDecls.concat pd) modulesToOpen openendModules

    /--
    Adds a single module to open (`openModule`) to the AST
    -/
    def addModuleToOpen (om : openModule)
      | mk name modulVariables sigDecls functionDecls factDecls assertDecls
        predDecls modulesToOpen openendModules =>
          AST.mk name modulVariables sigDecls functionDecls factDecls
          assertDecls predDecls (modulesToOpen.concat om) openendModules

    /--
    Adds a single opened module (`AST`) to the AST
    -/
    def addOpenedModule (ast : AST) (om : AST) : AST :=
      match ast with
        | mk name modulVariables sigDecls functionDecls factDecls assertDecls
          predDecls modulesToOpen openendModules =>
            AST.mk name modulVariables sigDecls functionDecls factDecls
            assertDecls predDecls modulesToOpen (openendModules.concat om)

  end AST

end Alloy
