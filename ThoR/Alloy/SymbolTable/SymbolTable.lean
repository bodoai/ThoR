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

open Lean

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

end Alloy
