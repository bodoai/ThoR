/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax
import ThoR.Alloy.Syntax.Predicate

open Shared

namespace Alloy

  /--
  This structure represents a (Lean) command declaration
  of either an definition (def) or axiom.
  -/
  structure commandDecl where
    mk :: (name : String)
          (args : List (predArg) := []) -- empty if axiom
          (formulas : List (formula)) -- formulas in an Alloy pred or an Alloy fact
          (requiredDefs : List (String)) -- only for Lean Infoview
          (requiredVars : List (String)) -- only for Lean Infoview
          (predCalls : List (List (String))) -- called predicates
          (relationCalls : List (String)) -- called relations
  deriving Repr

  namespace commandDecl

  /--
  Generates a String representation from the type.

  Note that formulas := {cd.formulas},
  is not included, since it is irrelevant for the user here
  but needed to form the commands in Commands.Lean
  -/
  def toString (cd : commandDecl) : String :=
    /-
    -/
    s!"commandDeclaration : \{
      name := {cd.name},
      args := {cd.args},
      required definitions := {cd.requiredDefs},
      required variables := {cd.requiredVars},
      called predicates := {cd.predCalls},
      called relations := {cd.relationCalls}
    }"

  instance : ToString commandDecl where
    toString := toString

  end commandDecl

end Alloy
