/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.Formula.formula
import ThoR.Alloy.Syntax.Predicate.PredArg.predArg
import ThoR.Alloy.SymbolTable.varDecl

open Shared

namespace Alloy

  /--
  This structure represents a (Lean) command declaration
  of either an definition (def) or axiom.
  -/
  inductive commandDecl where
    | mk  (name : String)
          (args : List (predArg) := []) -- empty if axiom
          (formulas : List (formula)) -- formulas in an Alloy pred or an Alloy fact
          (requiredDefs : List (String)) -- only for Lean Infoview
          (requiredVars : List (String)) -- only for Lean Infoview
          (predCalls : List (List (String))) -- called predicates
          (relationCalls : List (varDecl)) -- called relations
          (signatureCalls : List (commandDecl × List (varDecl))) -- called signatures
  deriving Repr
  namespace commandDecl

    def name | mk n _ _ _ _ _ _ _ => n
    def args | mk _ args _ _ _ _ _ _ => args
    def formulas | mk _ _ formulas _ _ _ _ _ => formulas
    def requiredDefs | mk _ _ _ requiredDefs _ _ _ _ => requiredDefs
    def requiredVars | mk _ _ _ _ requiredVars _ _ _ => requiredVars
    def predCalls | mk _ _ _ _ _ predCalls _ _ => predCalls
    def relationCalls | mk _ _ _ _ _ _ relationCalls _ => relationCalls
    def signatureCalls | mk _ _ _ _ _ _ _ signatureCalls => signatureCalls

    instance : Inhabited commandDecl where
      default :=
        commandDecl.mk
          (name := default)
          (args := default)
          (formulas := default)
          (requiredDefs := default)
          (requiredVars := default)
          (predCalls := default)
          (relationCalls := default)
          (signatureCalls := default)

  /--
  Generates a String representation from the type.
  -/
  partial def toString (cd : commandDecl) : String :=
    let sigCallsString :=
      cd.signatureCalls.map fun sc =>
        s!"({toString sc.1} {sc.2})"
    s!"commandDeclaration : \{
      name := {cd.name},
      args := {cd.args},
      required definitions := {cd.requiredDefs},
      required variables := {cd.requiredVars},
      called predicates := {cd.predCalls},
      called relations := {cd.relationCalls},
      called signatures := {sigCallsString},
      formulas := {cd.formulas}
    }"

  instance : ToString commandDecl where
    toString := toString

  end commandDecl

end Alloy
