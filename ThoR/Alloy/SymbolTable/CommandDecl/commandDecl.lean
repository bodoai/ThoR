/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.Formula.formula
import ThoR.Alloy.Syntax.Predicate.PredArg.predArg
import ThoR.Alloy.Syntax.Function.FunctionArg.functionArg
import ThoR.Alloy.Syntax.Function.FunctionIfDecl.functionIfDecl
import ThoR.Alloy.SymbolTable.VarDecl.varDecl

open Shared

namespace Alloy

  /--
  This type represents the type that is created
  that is created if you evaluate the command
  -/
  inductive commandType where
    | fact
    | assert
    | pred
    | function
  deriving Repr, BEq

  instance : ToString commandType where
    toString (ct) :=
      match ct with
        | commandType.fact => "fact"
        | commandType.assert => "assert"
        | commandType.pred => "pred"
        | commandType.function => "function"

  /--
  This inductive type represents a (Lean) command declaration
  of either an definition (def) or axiom.
  -/
  inductive commandDecl where
    | mk  (name : String)
          (commandType : commandType := commandType.pred)
          (predArgs : List (predArg × varDecl) := [])
          (functionArgs : List (functionArg × varDecl) := [])
          (functionReturnType : typeExpr := default)
          (formulas : List (formula) := []) -- formulas (used in preds, axioms, asserts)
          (expressions : List (expr) := []) -- expressiosn (used in functions)
          (ifExpressions : List (functionIfDecl) := [])
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
          (predCalls : List (commandDecl × List (expr × List (String × List (varDecl)))))
          (functionCalls : List (commandDecl × List (expr × List (String × List (varDecl)))))
          (relationCalls : List (String × List (varDecl))) -- called relations
          (signatureCalls : List (String × List (varDecl))) -- called signatures
  deriving Repr
  namespace commandDecl

    def name | mk n _ _ _ _ _ _ _ _ _ _ _ _ _ => n
    def commandType | mk  _ commandType _ _ _ _ _ _ _ _ _ _ _ _ => commandType
    def predArgs | mk _ _ predArgs _ _ _ _ _ _ _ _ _ _ _ => predArgs
    def functionArgs | mk _ _ _ functionArgs _ _ _ _ _ _ _ _ _ _ => functionArgs
    def functionReturnType | mk _ _ _ _ functionReturnType _ _ _ _ _ _ _ _ _ => functionReturnType
    def formulas | mk _ _ _ _ _ formulas _ _ _ _ _ _ _ _ => formulas
    def expressions | mk _ _ _ _ _ _ expressions _ _ _ _ _ _ _ => expressions
    def ifExpressions | mk _ _ _ _ _ _ _ ifExpressions _ _ _ _ _ _ => ifExpressions
    def requiredDefs | mk _ _ _ _ _ _ _ _ requiredDefs _ _ _ _ _ => requiredDefs
    def requiredVars | mk _ _ _ _ _ _ _ _ _ requiredVars _ _ _ _ => requiredVars
    def predCalls | mk _ _ _ _ _ _ _ _ _ _ predCalls _ _ _ => predCalls
    def functionCalls | mk _ _ _ _ _ _ _ _ _ _ _ functionCalls _  _ => functionCalls
    def relationCalls | mk _ _ _ _ _ _ _ _ _ _ _ _ relationCalls _ => relationCalls
    def signatureCalls | mk _ _ _ _ _ _ _ _ _ _ _ _ _ signatureCalls => signatureCalls

    instance : Inhabited commandDecl where
      default :=
        commandDecl.mk
          (name := default)
          (formulas := default)
          (expressions := default)
          (requiredDefs := default)
          (requiredVars := default)
          (predCalls := default)
          (functionCalls := default)
          (relationCalls := default)
          (signatureCalls := default)

    def updateFormulas
      (formulas : List (formula))
        | mk
            name
            commandType
            predArgs
            functionArgs
            functionReturnType
            _
            expressions
            ifExpressions
            requiredDefs
            requiredVars
            predCalls
            functionCalls
            relationCalls
            signatureCalls =>
          mk
            name
            commandType
            predArgs
            functionArgs
            functionReturnType
            formulas
            expressions
            ifExpressions
            requiredDefs
            requiredVars
            predCalls
            functionCalls
            relationCalls
            signatureCalls

    def updateExpressions
      (expressions : List (expr))
        | mk
            name
            commandType
            predArgs
            functionArgs
            functionReturnType
            formulas
            _
            ifExpressions
            requiredDefs
            requiredVars
            predCalls
            functionCalls
            relationCalls
            signatureCalls =>
          mk
            name
            commandType
            predArgs
            functionArgs
            functionReturnType
            formulas
            expressions
            ifExpressions
            requiredDefs
            requiredVars
            predCalls
            functionCalls
            relationCalls
            signatureCalls

  def isPredicate (cd : commandDecl) : Bool :=
    cd.commandType == commandType.pred

  def isFact (cd : commandDecl) : Bool :=
    cd.commandType == commandType.fact

  def isAssert (cd : commandDecl) : Bool :=
    cd.commandType == commandType.assert

  def isFunction (cd : commandDecl) : Bool :=
    cd.commandType == commandType.function

  /--
  Generates a String representation from the type.
  -/
  partial def toString (cd : commandDecl) : String :=
    let predCallsString :=
      cd.predCalls.map fun pc =>
        s!"({toString pc.1} {pc.2})"
    let functionCallsString :=
      cd.functionCalls.map fun fc =>
        s!"({toString fc.1} {fc.2})"

    s!"commandDeclaration : \{
        name := {cd.name},
        commandType := {cd.commandType},
        { if cd.commandType == commandType.pred then
            s!"args := {cd.predArgs}, \n"
          else "" }\
        { if cd.commandType == commandType.function then
            s!"args := {cd.functionArgs},\n "
          else "" }\
        { if cd.commandType == commandType.function then
            s!"functionReturnType := {cd.functionReturnType}, \n"
          else "" }\
        required definitions := {cd.requiredDefs},
        required variables := {cd.requiredVars},
        { if
            cd.commandType != commandType.function
          then
            s!"called predicates := {predCallsString}, \n"
          else "" }\
        called functions := {functionCallsString},
        called relations := {cd.relationCalls},
        called signatures := {cd.signatureCalls},
        { if
            cd.commandType != commandType.function
          then
            s!"formulas := {cd.formulas}, \n"
          else "" }\
        { if
            cd.commandType == commandType.function &&
            !cd.expressions.isEmpty
          then
            s!"expressions := {cd.expressions},"
          else "" }
        { if
            cd.commandType == commandType.function &&
            !cd.ifExpressions.isEmpty
          then
            s!"ifExpressions := {cd.ifExpressions}"
          else "" }
    }"

  instance : ToString commandDecl where
    toString := toString

  end commandDecl

end Alloy
