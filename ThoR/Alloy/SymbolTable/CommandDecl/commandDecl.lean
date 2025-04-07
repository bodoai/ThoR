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

    def updatePredCalls
      (predCalls : List (commandDecl × List (expr × List (String × List (varDecl)))))
        | mk
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
            _
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

    def updateFunctionCalls
      (functionCalls : List (commandDecl × List (expr × List (String × List (varDecl)))))
        | mk
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
            _
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
  partial def toString
      (cd : commandDecl)
      (inner_space_count := 3)
      (outer_space_count := 1)
      (leading_new_line := false)
      : String := Id.run do

      let mut inner_spaces : String := ""
      for _ in [0:inner_space_count] do
        inner_spaces := inner_spaces ++ " "

      let mut outer_spaces : String := ""
      for _ in [0:outer_space_count] do
        outer_spaces := outer_spaces ++ " "

      let predCallsString :=
        cd.predCalls.map fun pc =>
          pc.1.toString
            (inner_space_count := (inner_space_count + 3))
            (outer_space_count := inner_space_count + 1)
            (leading_new_line := true)
          ++
          List.toString pc.2

      let relationCallsString :=
        cd.relationCalls.map fun rc =>
          "\n" ++ inner_spaces ++ " " ++
          ToString.toString rc.1 ++
          ToString.toString
            (rc.2.map fun vd =>
              vd.toString
                (inner_space_count := (inner_space_count + 4))
                (outer_space_count := inner_space_count + 2)
                (leading_new_line := true)
            )

      let mut signatureCallsString := "["
      for signatureCall in cd.signatureCalls do
        signatureCallsString :=
          signatureCallsString ++
          "\n" ++ inner_spaces ++ " " ++
          ToString.toString signatureCall.1 ++
          " " ++ "["

        for varDecl in signatureCall.2 do
          signatureCallsString :=
            signatureCallsString ++
            varDecl.toString
              (inner_space_count := (inner_space_count + 4))
              (outer_space_count := inner_space_count + 2)
              (leading_new_line := true) ++
            "\n" ++ inner_spaces ++ " "

        signatureCallsString :=
          signatureCallsString ++
          "]"

        if cd.signatureCalls.getLast! != signatureCall then
          signatureCallsString :=
          signatureCallsString ++
          ","

      signatureCallsString :=
        signatureCallsString ++ "\n" ++
        inner_spaces ++ "]"

      let predArgsString :=
        cd.predArgs.map fun pa =>
          pa.1.toString
            (inner_space_count := (inner_space_count + 4))
            (outer_space_count := inner_space_count + 2)
            (leading_new_line := true) ++
          "," ++
          pa.2.toString
            (inner_space_count := (inner_space_count + 4))
            (outer_space_count := inner_space_count + 2)
            (leading_new_line := true)

      let result :=
        outer_spaces ++ "command declaration : ⦃ \n" ++
        inner_spaces ++ s!"name := {cd.name}" ++ "\n" ++
        inner_spaces ++ s!"command type := {cd.commandType}," ++ "\n" ++
        ( if cd.commandType == commandType.pred then
            inner_spaces ++ s!"args := {predArgsString}," ++ "\n" else ""
        ) ++
        ( if cd.commandType == commandType.function then
            inner_spaces ++s!"args := {cd.functionArgs}," ++ "\n" else ""
        ) ++
        ( if cd.commandType == commandType.function then
            inner_spaces ++
            s!"function return type := {cd.functionReturnType}" ++ "\n"
          else ""
        ) ++
        inner_spaces ++ s!"required definitions := {cd.requiredDefs}," ++
        "\n" ++
        inner_spaces ++ s!"required variables := {cd.requiredVars}," ++
        "\n" ++
        ( if cd.commandType != commandType.function then
            inner_spaces ++
            s!"called predicates := {predCallsString}," ++ "\n"
          else ""
        ) ++
        inner_spaces ++ s!"called relations := {relationCallsString}," ++
        "\n" ++
        inner_spaces ++ s!"called signatures := {signatureCallsString}," ++
        "\n" ++
        ( if cd.commandType != commandType.function then
            inner_spaces ++ s!"formulas := {cd.formulas}," ++ "\n"
          else ""
        ) ++
        ( if cd.commandType == commandType.function then
            inner_spaces ++ s!"expressions := {cd.expressions}" ++ "\n"
          else ""
        ) ++
        outer_spaces ++ "⦄"

      if leading_new_line then
        "\n" ++ result
      else
        result

  instance : ToString commandDecl where
    toString := toString

  end commandDecl

end Alloy
