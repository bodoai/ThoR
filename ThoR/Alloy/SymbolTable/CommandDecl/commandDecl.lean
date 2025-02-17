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
          (isPredicate : Bool := false)
          (args : List (predArg) := []) -- empty if axiom
          (formulas : List (formula)) -- formulas in an Alloy pred or an Alloy fact
          (requiredDefs : List (String)) -- only for Lean Infoview
          (requiredVars : List (String)) -- only for Lean Infoview
          /-
          a list of called predicates, contains the called predicate and
          a list of the calls in the given arguments and the expression
          of the argument to simplify checks. Note that there can
          be multiple calls in one argumen e.g. t - t => t is called two times
          the innermost list can contain multiple varDecls IF the call is
          ambigous.

          Possible improvement on clarity:
          Make a Structure that conveys the meaning better?
          -/
          (predCalls : List (commandDecl × List (expr × List (List (varDecl)))))
          (relationCalls : List (List (varDecl))) -- called relations
          (signatureCalls : List (List (varDecl))) -- called signatures
  deriving Repr
  namespace commandDecl

    def name | mk n _ _ _ _ _ _ _ _ => n
    def isPredicate | mk _ isPredicate _ _ _ _ _ _ _ => isPredicate
    def args | mk _ _ args _ _ _ _ _ _ => args
    def formulas | mk _ _ _ formulas _ _ _ _ _ => formulas
    def requiredDefs | mk _ _ _ _ requiredDefs _ _ _ _ => requiredDefs
    def requiredVars | mk _ _ _ _ _ requiredVars _ _ _ => requiredVars
    def predCalls | mk _ _ _ _ _ _ predCalls _ _ => predCalls
    def relationCalls | mk _ _ _ _ _ _ _ relationCalls _ => relationCalls
    def signatureCalls | mk _ _ _ _ _ _ _ _ signatureCalls => signatureCalls

    instance : Inhabited commandDecl where
      default :=
        commandDecl.mk
          (name := default)
          (isPredicate := default)
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
    let predCallsString :=
      cd.predCalls.map fun pc =>
        s!"({toString pc.1} {pc.2})"
    s!"commandDeclaration : \{
      name := {cd.name},
      isPredicate := {cd.isPredicate},
      args := {cd.args},
      required definitions := {cd.requiredDefs},
      required variables := {cd.requiredVars},
      called predicates := {predCallsString},
      called relations := {cd.relationCalls},
      called signatures := {cd.signatureCalls},
      formulas := {cd.formulas}
    }"

  instance : ToString commandDecl where
    toString := toString

  end commandDecl

end Alloy
