/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Formula.formula
import ThoR.Alloy.SymbolTable.CommandDecl.commandDecl
import ThoR.Alloy.Syntax.Predicate.PredDecl.predDecl

import ThoR.Shared.Syntax.Relation.Expr.exprService
import ThoR.Shared.Syntax.TypeExpr.typeExprService
import ThoR.Shared.Syntax.Algebra.AlgExpr.algExprService

import ThoR.Relation.Elab
import ThoR.Relation.SubType
import ThoR.Relation.Quantification
import ThoR.Alloy.Config

import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.UnhygienicUnfolder

open Alloy ThoR ThoR.Quantification
open Lean ThoR Config

namespace Shared.formula

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given formula `f`
  -/
  partial def replaceCalls
    (f: formula)
    (callables : List (varDecl))
    : formula := Id.run do
      match f with
        | formula.string _ =>

          /-
          there can be only calls the preds here.
          These currently do not need replacers
          -/
          return f

        | formula.pred_with_args n pas =>
          formula.pred_with_args
            n
            (pas.map fun pa =>
              pa.replaceCalls callables)

        | formula.unaryRelBoolOperation op e =>
          formula.unaryRelBoolOperation
            op
            (e.replaceCalls callables)

        | formula.unaryLogicOperation op f =>
          formula.unaryLogicOperation
            op
            (f.replaceCalls callables)

        | formula.binaryLogicOperation op f1 f2 =>
          formula.binaryLogicOperation
            op
            (f1.replaceCalls callables)
            (f2.replaceCalls callables)

        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          formula.tertiaryLogicOperation
            op
            (f1.replaceCalls callables)
            (f2.replaceCalls callables)
            (f3.replaceCalls callables)

        | formula.algebraicComparisonOperation op ae1 ae2 =>
          formula.algebraicComparisonOperation op ae1 ae2

        | formula.relationComarisonOperation op e1 e2 =>
          formula.relationComarisonOperation
            op
            (e1.replaceCalls callables)
            (e2.replaceCalls callables)

        | formula.quantification q d n te forms =>
          formula.quantification
            q
            d
            n
            (te.replaceCalls callables)
            (forms.map fun f => f.replaceCalls callables)

        | formula.letDeclaration name value body =>
          formula.letDeclaration
            name
            (value.replaceCalls callables)
            (body.map fun f => f.replaceCalls callables)

  partial def toTermOutsideBlock
    (f : formula)
    (availableAlloyData : List (alloyData) := [])
    (localContextUserNames : List Name := [])
    : Except String ((Term)) := do
    match f with
      | formula.string s => do
        let mut possibleDecls := []
        for alloyData in availableAlloyData do
          let possibleMatches :=
            (alloyData.st.assertDecls ++
            alloyData.st.axiomDecls ++
            alloyData.st.defDecls).filter
              fun cd => cd.name == s

          if !possibleMatches.isEmpty then
            possibleDecls := possibleDecls.concat
              (alloyData.st.name, possibleMatches)

        if !possibleDecls.isEmpty then
          if
            -- if there are matches in more than one module
            possibleDecls.length > 1 ||
            -- or more than one match in a module (this should be impossible)
            possibleDecls.any fun pv => pv.2.length > 1
          then
            throw s!"The call to {s} is ambiguous. \
            There are multiple declared definitions which it could refer to ({possibleDecls})"

          let declsOfBlock := possibleDecls[0]!
          let calledBlockName := declsOfBlock.1
          let calledCommandDecl := (declsOfBlock.2[0]!)

          let calledNameComponents :=
            calledBlockName.components ++
            match calledCommandDecl.commandType with
              | commandType.assert => [`asserts, s.toName]
              | commandType.fact => [`facts, s.toName]
              | commandType.pred => [`preds, s.toName]
              | commandType.function => [`functions, s.toName]

          let calledName := Name.fromComponents calledNameComponents
          return unhygienicUnfolder `((@$(mkIdent calledName) $(baseType.ident) _ _))

        return unhygienicUnfolder `($(mkIdent s.toName))

      | formula.pred_with_args p pa => do
        let mut term :=
          `((
              ∻ $(mkIdent p.toName)
            ))

        for arg in pa do
          let argTerm ←
            arg.toTermOutsideBlock
              (availableAlloyData:= availableAlloyData)
              (localContextUserNames := localContextUserNames)

          term :=
              `(term |
                $(unhygienicUnfolder term)
                $(argTerm)
              )

        return unhygienicUnfolder term

      | formula.unaryRelBoolOperation op e =>
        let eTerm ←
          e.toTermOutsideBlock
            (availableAlloyData:= availableAlloyData)
            (localContextUserNames := localContextUserNames)

        return unhygienicUnfolder `(( $(op.toTerm)
            $(eTerm)
          ))

      | formula.unaryLogicOperation op f =>
        let fTerm ← f.toTermOutsideBlock availableAlloyData localContextUserNames
        return unhygienicUnfolder `(term | ( $(op.toTerm) $(fTerm)))

      | formula.binaryLogicOperation op f1 f2 =>
        let f1Term ←
          f1.toTermOutsideBlock availableAlloyData localContextUserNames
        let f2Term ←
          f2.toTermOutsideBlock availableAlloyData localContextUserNames
        return unhygienicUnfolder `(( $(op.toTerm)
            $(f1Term)
            $(f2Term)
          ))

      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        let f1Term ←
          f1.toTermOutsideBlock availableAlloyData localContextUserNames
        let f2Term ←
          f2.toTermOutsideBlock availableAlloyData localContextUserNames
        let f3Term ←
          f3.toTermOutsideBlock availableAlloyData localContextUserNames
        return unhygienicUnfolder `(( $(op.toTerm)
            $(f1Term)
            $(f2Term)
            $(f3Term)
          ))

      | formula.algebraicComparisonOperation op algE1 algE2 =>
        return unhygienicUnfolder
          `(($(op.toTerm) $(← algE1.toTermOutsideBlock) $(← algE2.toTermOutsideBlock)))

      | formula.relationComarisonOperation op e1 e2 =>
        let e1Term ←
          e1.toTermOutsideBlock
            (availableAlloyData:= availableAlloyData)
            (localContextUserNames := localContextUserNames)
        let e2Term ←
          e2.toTermOutsideBlock
            (availableAlloyData:= availableAlloyData)
            (localContextUserNames := localContextUserNames)

        return unhygienicUnfolder `(( $(op.toTerm)
            $(e1Term)
            $(e2Term)
          ))

      | formula.quantification q disjunction n te f => do

        let names := (n.map fun (name) => mkIdent name.toName).reverse

        -- one form ist present -> see syntax (+)
        let firstForm := f[0]!
        let firstFTerm ← firstForm.toTermOutsideBlock availableAlloyData localContextUserNames

        let mut completefTerm : Unhygienic (Term) :=
          `(term | $(firstFTerm))

        for form in f.drop 1 do
          let fTerm ←
            form.toTermOutsideBlock availableAlloyData localContextUserNames

          completefTerm :=
            `(( $(unhygienicUnfolder completefTerm) ∧
                ($(fTerm))
              ))

        completefTerm :=
          `((
            $(mkIdent ``Formula.prop)
            ($(unhygienicUnfolder completefTerm))
            ))

        -- singular parameter is var constructor
        if names.length == 1 then
            return unhygienicUnfolder `(($(mkIdent ``Formula.var) $(q.toTerm)) (
              fun ( $(names[0]!) : ∷ $((te.toStringRb).toSyntaxOutsideBlock))
                => $(unhygienicUnfolder completefTerm)))

        -- multiple parameter is Group constructor
        else
          let mut formulaGroup :=
            `(($(mkIdent ``Group.var) (
              fun ( $(names[0]!) : ∷ $((te.toStringRb).toSyntaxOutsideBlock))
                => $(mkIdent ``Group.formula) $(unhygienicUnfolder completefTerm))))
          for n in (names.drop 1) do
            formulaGroup :=
              `(($(mkIdent ``Group.var) (
                fun ( $(n) : ∷ $((te.toStringRb).toSyntaxOutsideBlock))
                  => $(unhygienicUnfolder formulaGroup))))
          if disjunction then
            formulaGroup :=
              `(( $(mkIdent ``Formula.disj)
                  $(mkIdent ``Shared.quant.all)
                  $(unhygienicUnfolder formulaGroup)
                ))
          else
            formulaGroup :=
              `(( $(mkIdent ``Formula.group)
                  $(mkIdent ``Shared.quant.all)
                  $(unhygienicUnfolder formulaGroup)
                ))

          return unhygienicUnfolder formulaGroup

      | formula.letDeclaration name value body =>
        let nameT := mkIdent name
        let valueT :=
          (← value.toTermOutsideBlock availableAlloyData localContextUserNames)
        let e_bodyT :=
          (body.map fun e =>
            e.toTermOutsideBlock availableAlloyData localContextUserNames
            )
        let mut bodyTermList : List Term := []
        for elem in e_bodyT do
          match elem with
            | Except.error msg => throw msg
            | Except.ok data => bodyTermList := bodyTermList.concat data

        if bodyTermList.isEmpty then throw s!"let {name}={value} has empty body"

        let mut bodyTerm := unhygienicUnfolder `(term | ($(bodyTermList[0]!)))
        for elem in bodyTermList do
          bodyTerm := unhygienicUnfolder `(bodyTerm ∧ ($(elem)))

        let letTerm := unhygienicUnfolder `(let $(nameT):ident := $(valueT):term; $(bodyTerm))

        return letTerm

  /--
  Generates a Lean term corosponding with the type
  -/
  private partial def toTerm'
    (f: formula)
    (blockName : Name)
    (variableNames : List (String)) -- to check if var or pred
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    -- names that have to be pure with no namespace (quantors and args)
    (pureNames : List (String) := [])
    : Except String (Unhygienic (Term)) := do

      match f with
      | formula.string s => do
        -- Quantors and args dont use namespaces
        if pureNames.contains s then
          return `($(mkIdent s.toName))

        else
          -- check if the ident is a variable or def
          if variableNames.contains s then
            return `((
                      ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
                    ))

          else
            return `((
                      ∻ $(mkIdent s!"{blockName}.preds.{s}".toName)
                    ))

      | formula.pred_with_args p pa => do
        let mut term :=
          `((
              ∻ $(mkIdent s!"{blockName}.preds.{p}".toName)
            ))

        let possibleCalledPredicates :=
          (callablePredicates.filter fun cp => cp.1.name == p)

        if possibleCalledPredicates.isEmpty || possibleCalledPredicates.length > 1 then
          panic!
            s!"Called Preds is Empty or more than one \
            in formulaService {possibleCalledPredicates}"

        let calledPredicate := possibleCalledPredicates[0]!

        let calledArgsVarDecls :=
          (calledPredicate.1.predArgs.map fun cp =>
            cp.1.names.map fun _ =>
              cp.2).flatten

        for index in [0:pa.length] do

          --let definedArg := calledPredArgs[index]!

          let vd := calledArgsVarDecls[index]!

          let typeName :=
            (if vd.isRelation then
              vd.getFullRelationName
            else
              vd.getFullSignatureName)

          let typeReplacementName :=
            (if vd.isRelation then
              vd.getRelationReplacementName
            else
              vd.getSignatureReplacementName)

          let calledArg := pa[index]!
          let calledVarDecls_of_arg_to_cast ←
            calledArg.getCalledVariables callableVariables
          let calledVarDecls_of_arg_to_cast_joined :=
            (calledVarDecls_of_arg_to_cast.map fun a => a.2).flatten

          let cast_type_as_expr_string := expr.string typeName.toString
          let cast_type_as_expr_string_rb := cast_type_as_expr_string.toStringRb
          let cast_type_as_type_expr_relExpr := typeExpr.relExpr cast_type_as_expr_string_rb

          let cast_type_equals_called_var_type :=
            -- the type must be clear (only one called var)
            (calledVarDecls_of_arg_to_cast_joined.length == 1) &&
            /-
            get the type, stringify it and compare it to the
            replacerName of the type we try to cast to
            (the replacer is only needed because its "prettier"
            to use the alias for casting, otherwise you could use
            the replacer on both sides (its the actual name))
            -/
            (
              let cv := (calledVarDecls_of_arg_to_cast_joined[0]!)
              cv.type.toString == typeReplacementName
            )

          if
            cast_type_as_expr_string == calledArg ||
            cast_type_as_expr_string_rb == calledArg ||
            cast_type_equals_called_var_type
          then
            term :=
              `(term |
                $(unhygienicUnfolder term)
                $(← calledArg.toTermFromBlock blockName pureNames)
              )

          else

            let castCommand : Unhygienic Term :=
              `(term |
                cast
                ($(← calledArg.toTermFromBlock blockName pureNames):term)
                ∷ $(cast_type_as_type_expr_relExpr.toSyntax blockName))

            term :=
              `(term |
                $(unhygienicUnfolder term)
                $(unhygienicUnfolder castCommand)
              )

        return term

      | formula.unaryRelBoolOperation op e =>
        return `(( $(op.toTerm)
            $(← e.toTermFromBlock
              blockName pureNames)
          ))

      | formula.unaryLogicOperation op f =>
        let fTerm ← f.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        return `(term | ( $(op.toTerm) $(unhygienicUnfolder fTerm)))

      | formula.binaryLogicOperation op f1 f2 =>
        let f1Term ←
          f1.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        let f2Term ←
          f2.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        return `(( $(op.toTerm)
            $(unhygienicUnfolder f1Term)
            $(unhygienicUnfolder f2Term)
          ))

      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        let f1Term ←
          f1.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        let f2Term ←
          f2.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        let f3Term ←
          f3.toTerm' blockName variableNames callableVariables callablePredicates pureNames
        return `(( $(op.toTerm)
            $(unhygienicUnfolder f1Term)
            $(unhygienicUnfolder f2Term)
            $(unhygienicUnfolder f3Term)
          ))

      | formula.algebraicComparisonOperation op ae1 ae2 =>
        return `(($(op.toTerm) $(← ae1.toTerm blockName) $(← ae2.toTerm blockName)))

      | formula.relationComarisonOperation op e1 e2 =>
        return `(( $(op.toTerm)
            $(← e1.toTermFromBlock
              blockName pureNames)
            $(← e2.toTermFromBlock
              blockName pureNames)
          ))

      | formula.quantification q disjunction n te f => do

        let names := (n.map fun (name) => mkIdent name.toName).reverse

        /-add quant vars here so you can get their type later-/
        let quantVarDecls :=
          n.map fun nam =>
            varDecl.mk
              (name := nam)
              (isQuantor := true)
              (isOpened := false)
              (openedFrom := "this")
              (isRelation := false)
              (relationOf := default)
              (type := te)
              (requiredDecls := [])

        -- one form ist present -> see syntax (+)
        let firstForm := f[0]!
        let firstFTerm ←
          firstForm.toTerm'
            blockName variableNames (callableVariables ++ quantVarDecls) callablePredicates
            (pureNames.append n)

        let mut completefTerm : Unhygienic (Term) :=
          `(term | $(unhygienicUnfolder firstFTerm))

        for form in f.drop 1 do
          let fTerm ←
            form.toTerm'
              blockName variableNames (callableVariables ++ quantVarDecls) callablePredicates
              (pureNames.append n)

          completefTerm :=
            `(( $(unhygienicUnfolder completefTerm) ∧
                ($(unhygienicUnfolder fTerm))
              ))

        completefTerm :=
          `((
            $(mkIdent ``Formula.prop)
            ($(unhygienicUnfolder completefTerm))
            ))

        -- singular parameter is var constructor
        if names.length == 1 then
            return `(($(mkIdent ``Formula.var) $(q.toTerm)) (
              fun ( $(names[0]!) : ∷ $((te.toStringRb).toSyntax blockName))
                => $(unhygienicUnfolder completefTerm)))

        -- multiple parameter is Group constructor
        else
          let mut formulaGroup :=
            `(($(mkIdent ``Group.var) (
              fun ( $(names[0]!) : ∷ $((te.toStringRb).toSyntax blockName))
                => $(mkIdent ``Group.formula) $(unhygienicUnfolder completefTerm))))
          for n in (names.drop 1) do
            formulaGroup :=
              `(($(mkIdent ``Group.var) (
                fun ( $(n) : ∷ $((te.toStringRb).toSyntax blockName))
                  => $(unhygienicUnfolder formulaGroup))))
          if disjunction then
            formulaGroup :=
              `(( $(mkIdent ``Formula.disj)
                  $(mkIdent ``Shared.quant.all)
                  $(unhygienicUnfolder formulaGroup)
                ))
          else
            formulaGroup :=
              `(( $(mkIdent ``Formula.group)
                  $(mkIdent ``Shared.quant.all)
                  $(unhygienicUnfolder formulaGroup)
                ))

          return formulaGroup

      | formula.letDeclaration name value body =>
        let nameT := mkIdent name
        let valueT :=
          unhygienicUnfolder
            (← value.toTerm' blockName variableNames callableVariables callablePredicates)
        let e_bodyT :=
          (body.map fun e =>
            e.toTerm' blockName variableNames callableVariables callablePredicates
            )
        let mut bodyTermList : List Term := []
        for elem in e_bodyT do
          match elem with
            | Except.error msg => throw msg
            | Except.ok data => bodyTermList := bodyTermList.concat (unhygienicUnfolder data)


        if bodyTermList.isEmpty then throw s!"let {name}={value} has empty body"

        let mut bodyTerm := `(term | ($(bodyTermList[0]!)))
        for elem in bodyTermList do
          bodyTerm := `(bodyTerm ∧ ($(elem)))

        let letTerm := `(let $(nameT):ident := $(valueT):term; $(unhygienicUnfolder bodyTerm))

        return letTerm

  def toTerm
    (f: formula)
    (blockName : Name)
    (variableNames : List (String)) -- to check if var or pred
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    -- names that have to be pure with no namespace (quantors and args)
    (pureNames : List (String) := [])
    : Except String (Term) := do
    let x := toTerm' f blockName variableNames callableVariables callablePredicates pureNames
    match x with
      | Except.error msg => throw msg
      | Except.ok data => return unhygienicUnfolder data

  partial def toType_withoutIf
    (f : Formula_without_if)
    (signatureFactSigNames : List String := [])
    : Except String formula := do
      match f with
        | `(formula_without_if| ( $fwi:formula_without_if )) =>
          return ← toType_withoutIf fwi

        | `(formula_without_if| $name:ident) =>
          return formula.string name.getId.toString

        | `(formula_without_if| $predName:ident [$predargs,*]) =>
          let mut arguments_typed := []
          for argument in predargs.getElems do
            arguments_typed := arguments_typed.concat
              (← expr.toType argument signatureFactSigNames)

          return formula.pred_with_args
            predName.getId.toString
            arguments_typed

        | `(formula_without_if| $op:unRelBoolOp $expression:expr ) =>
          return formula.unaryRelBoolOperation
            (← unRelBoolOp.toType op) (← expr.toType expression signatureFactSigNames)

        | `(formula_without_if| $op:unLogOp $f:formula_without_if ) =>
          return formula.unaryLogicOperation
            (← unLogOp.toType op) (← toType_withoutIf f)

        | `(formula_without_if| $form1:formula_without_if $op:binLogOp $form2:formula_without_if) =>
          return formula.binaryLogicOperation
            (← binLogOp.toType op) (← toType_withoutIf form1) (← toType_withoutIf form2)

        | `(formula_without_if|
            $algExpr1:algExpr
            $compOp:algCompareOp
            $algExpr2:algExpr) =>
          return formula.algebraicComparisonOperation
            (← algCompareOp.toType compOp)
            (← algExpr.toType algExpr1)
            (← algExpr.toType algExpr2)

        | `(formula_without_if|
            $expr1:expr
            $op:relCompareOp
            $expr2:expr) =>
          return formula.relationComarisonOperation
            (← relCompareOp.toType op)
            (← expr.toType expr1 signatureFactSigNames)
            (← expr.toType expr2 signatureFactSigNames)

        | `(formula_without_if|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula_without_if
            ) =>
          return formula.quantification
            (← quant.toType q)
            true
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            ([← toType_withoutIf form])

        | `(formula_without_if|
            $q:quant
            disj
            $names:ident,* :
            $typeExpression:typeExpr |
            { $form:formula_without_if* }
            ) =>

          let mut forms_typed := []
          for f in form do
            forms_typed := forms_typed.concat (← toType_withoutIf f)

          return formula.quantification
            (← quant.toType q)
            true
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            forms_typed

        | `(formula_without_if|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            $form:formula_without_if
            ) =>
          return formula.quantification
            (← quant.toType q)
            false
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            ([← toType_withoutIf form])

        | `(formula_without_if|
            $q:quant
            $names:ident,* :
            $typeExpression:typeExpr |
            {$form:formula_without_if*}
            ) =>
          let mut forms_typed := []
          for f in form do
            forms_typed := forms_typed.concat (← toType_withoutIf f)
          return formula.quantification
            (← quant.toType q)
            false
            (names.getElems.map fun (elem) => elem.getId.toString).toList
            (← typeExpr.toType typeExpression)
            forms_typed

        -- let declaration
        | `(formula_without_if | $alloy_let_decl:alloyLetDecl) =>
          match alloy_let_decl with
            | `(alloyLetDecl | let $name:ident = $value:formula_without_if | $body:formula_without_if) =>
              return formula.letDeclaration
                (name := name.getId)
                (value := ← formula.toType_withoutIf value)
                (body := [← formula.toType_withoutIf body])
            | `(alloyLetDecl |
                let $name:ident = $value:formula_without_if |
                { $body:formula_without_if* }
              ) =>

              let mut body_typed := []
              for f in body do
                body_typed := body_typed.concat (← formula.toType_withoutIf f)

              return formula.letDeclaration
                (name := name.getId)
                (value := ←formula.toType_withoutIf value)
                (body := body_typed)
            | syntx => throw s!"No match implemented in \
              formulaSerivce.toType (let match) \
              for '{syntx}'"

        | syntx => throw s!"No match implemented in \
              formulaSerivce.toType \
              for '{syntx}'"

  /--
  Parses the given syntax to the type
  -/
  partial def toType
    (f : Formula)
    (signatureFactSigNames : List String := [])
    : Except String formula := do
      match f with
        | `(formula| $fwi:formula_without_if) =>
          return ← toType_withoutIf fwi signatureFactSigNames
        | `(formula| $form1:formula => $form2:formula else $form3:formula) =>
          return formula.tertiaryLogicOperation terLogOp.ifelse
              (← toType form1) (← toType form2) (← toType form3)

        | syntx => throw s!"No match implemented in \
            formulaService.toType \
            for '{syntx}'"

  /--
  Returns the required definitions for the formula to work in Lean
  -/
  partial def getReqDefinitions
    (f : formula)
    : List (String) := Id.run do
      match f with
        | formula.string s => [s]
        | formula.pred_with_args p _ => [p]
        | formula.unaryRelBoolOperation _ _ => []
        | formula.unaryLogicOperation _ f => f.getReqDefinitions
        | formula.binaryLogicOperation _ f1 f2 =>
          f1.getReqDefinitions.append f2.getReqDefinitions
        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          (f1.getReqDefinitions.append f2.getReqDefinitions).append f3.getReqDefinitions
        | formula.algebraicComparisonOperation _ _ _ => []
        | formula.relationComarisonOperation _ _ _ => []
        | formula.quantification _ _ n _ f =>
          ((f.map fun form =>
            form.getReqDefinitions).flatten
              ).filter fun (elem) => !(n.contains elem)
        | formula.letDeclaration _ value body =>
          let value_rd := value.getReqDefinitions
          let body_rds := (body.map fun e => e.getReqDefinitions).flatten
          body_rds ++ value_rd

  /--
  Returns the required variables for the formula to work in Lean
  -/
  partial def getReqVariables
    (f : formula)
    : List (String) := Id.run do
      match f with
        | formula.string _ => []
        | formula.pred_with_args _ pa =>
          (pa.map fun (e) => e.getReqVariables).flatten
        | formula.unaryRelBoolOperation _ e => e.getReqVariables
        | formula.unaryLogicOperation _ f => f.getReqVariables
        | formula.binaryLogicOperation _ f1 f2 =>
          f1.getReqVariables ++ f2.getReqVariables
        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          f1.getReqVariables ++ f2.getReqVariables ++ f3.getReqVariables
        | formula.algebraicComparisonOperation _ ae1 ae2 =>
          ae1.getReqVariables ++ ae2.getReqVariables
        | formula.relationComarisonOperation _ e1 e2 =>
          e1.getReqVariables ++ e2.getReqVariables
        | formula.quantification _ _ n e f =>
          (((f.map fun form =>
            form.getReqVariables).flatten)
            ++ e.getReqVariables).filter
            fun (elem) => !(n.contains elem) -- quantor vars are not required
        | formula.letDeclaration name value body =>
          let value_rv := value.getReqVariables
          let body_rvs :=
            (body.map fun e => e.getReqVariables).flatten.filter
              -- the name is not required in the body
              fun elem => !(name.toString == elem)
          body_rvs ++ value_rv

  /--
  Gets all calls to the `callablePredicates`

  The result takes the form of a List of Tuples which contain called Predicates
  (as commandDecl) with the given arguments (as varDecl)
  -/
  partial def getCalledPredicates
    (f : formula)
    (callablePredicates : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      let callablePredicateNames := callablePredicates.map fun cp => cp.name

      match f with
        | formula.string s =>
          if callablePredicateNames.contains s then
            let index := callablePredicateNames.idxOf s
            let calledPredicate := callablePredicates[index]!
            return [(calledPredicate, [])]
          else
            return []

        | formula.pred_with_args predicate_name predicate_arguments =>
          if callablePredicateNames.contains predicate_name then
            let index := callablePredicateNames.idxOf predicate_name
            let calledPredicate := callablePredicates[index]!

            let mut calledArgumentVariables := []
            for arg in predicate_arguments do
              calledArgumentVariables :=
                calledArgumentVariables.concat
                  (arg, (← arg.getCalledVariables callableVariables))

            return [(calledPredicate, calledArgumentVariables)]
          else
            return []

        | formula.unaryLogicOperation _ f =>
          f.getCalledPredicates callablePredicates callableVariables

        | formula.binaryLogicOperation _ f1 f2 =>
          let f1_calls ← (f1.getCalledPredicates callablePredicates callableVariables)
          let f2_calls ← (f2.getCalledPredicates callablePredicates callableVariables)
          return f1_calls ++ f2_calls

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          let f1_calls ← (f1.getCalledPredicates callablePredicates callableVariables)
          let f2_calls ← (f2.getCalledPredicates callablePredicates callableVariables)
          let f3_calls ← (f3.getCalledPredicates callablePredicates callableVariables)
          return f1_calls ++ f2_calls ++ f3_calls

        | formula.quantification _ _ _ _ f =>
          let mut result := []
          for form in f do
            result := result ++ (← form.getCalledPredicates callablePredicates callableVariables)
          return result

        | formula.letDeclaration _ value body =>
          let value_cp ← value.getCalledPredicates callablePredicates callableVariables
          let mut body_cps := []
          for element in body do
            let calledPreds ← element.getCalledPredicates callablePredicates callableVariables
            body_cps := body_cps ++ calledPreds
          return body_cps ++ value_cp

        | _ => return []

  /--
  Gets all calls to the `callableVariables` which includes signatures and relations.

  The result is a list of the call (in string from) and a (possibly empty) list
  of the concrete possible called variables (in form of varDecls). If the inner
  list contains more than one varDecl, called variable is ambiguous and could
  be either.
  -/
  partial def getCalledVariables
    (f : formula)
    (callableVariables : List (varDecl))
    : Except String (List (String × List (varDecl))) := do

      match f with
        | formula.pred_with_args _ predicate_arguments =>
          let mut result : List (String × List varDecl) := []
          for pa in predicate_arguments do
            result := result ++ (← pa.getCalledVariables callableVariables)
          return result

        | formula.unaryRelBoolOperation _ e =>
          (e.getCalledVariables callableVariables)

        | formula.unaryLogicOperation _ f =>
          (f.getCalledVariables callableVariables)

        | formula.binaryLogicOperation _ f1 f2 =>
          let f1_calls ← (f1.getCalledVariables callableVariables)
          let f2_calls ← (f2.getCalledVariables callableVariables)
          return f1_calls ++ f2_calls

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          let f1_calls ← (f1.getCalledVariables callableVariables)
          let f2_calls ← (f2.getCalledVariables callableVariables)
          let f3_calls ← (f3.getCalledVariables callableVariables)
          return f1_calls ++ f2_calls ++ f3_calls

        | formula.relationComarisonOperation _ e1 e2 =>
          let e1_calls ← (e1.getCalledVariables callableVariables)
          let e2_calls ← (e2.getCalledVariables callableVariables)
          return e1_calls ++ e2_calls

        | formula.quantification _ _ names te f =>
          let typeExprRelCalls ← te.getCalledVariables callableVariables

          let quantVarDecls :=
            names.map fun n =>
              varDecl.mk
                (name := n)
                (isQuantor := true)
                (isOpened := false)
                (openedFrom := "this")
                (isRelation := false)
                (relationOf := default)
                (type := te)
                (requiredDecls := [])

          let mut result : List (String × List varDecl) := []
          for form in f do
            result := result ++ (← form.getCalledVariables (callableVariables ++ quantVarDecls))

          return typeExprRelCalls ++ result

        | formula.letDeclaration _ value body =>
          let value_cp ← value.getCalledVariables callableVariables
          let mut body_cps := []
          for element in body do
            let calledPreds ← element.getCalledVariables callableVariables
            body_cps := body_cps ++ calledPreds
          return body_cps ++ value_cp

        | _ => return []

  partial def simplifyDomainRestrictions
    (f : formula)
    (st : SymbolTable)
    : formula :=
    match f with
      | formula.pred_with_args p args =>
        pred_with_args p (args.map fun arg => arg.simplifyDomainRestrictions st)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation op (e.simplifyDomainRestrictions st)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation op (f.simplifyDomainRestrictions st)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.simplifyDomainRestrictions st)
          (f2.simplifyDomainRestrictions st)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
        op
        (f1.simplifyDomainRestrictions st)
        (f2.simplifyDomainRestrictions st)
        (f3.simplifyDomainRestrictions st)
      | formula.quantification q d n t f =>
        formula.quantification
        q
        d
        n
        (t.simplifyDomainRestrictions st)
        (f.map fun f => f.simplifyDomainRestrictions st)

      | formula.letDeclaration name value body =>
        formula.letDeclaration
          (name)
          (value.simplifyDomainRestrictions st)
          (body.map fun f => f.simplifyDomainRestrictions st)

      | _ => f

  partial def insertModuleVariables
    (f : formula)
    (moduleVariables openVariables : List (String))
    : formula :=
    match f with
      | formula.pred_with_args p args =>
        pred_with_args
          p
          (args.map fun arg =>
            arg.insertModuleVariables moduleVariables openVariables)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation
          op
          (e.insertModuleVariables moduleVariables openVariables)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation
          op
          (f.insertModuleVariables moduleVariables openVariables)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.insertModuleVariables moduleVariables openVariables)
          (f2.insertModuleVariables moduleVariables openVariables)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
        op
        (f1.insertModuleVariables moduleVariables openVariables)
        (f2.insertModuleVariables moduleVariables openVariables)
        (f3.insertModuleVariables moduleVariables openVariables)
      | formula.quantification q d n t f =>
        formula.quantification
        q
        d
        n
        (t.insertModuleVariables moduleVariables openVariables)
        (f.map fun f =>
          f.insertModuleVariables moduleVariables openVariables)

      | formula.letDeclaration name value body =>
        formula.letDeclaration
          (name)
          (value.insertModuleVariables moduleVariables openVariables)
          (body.map fun f => f.insertModuleVariables moduleVariables openVariables)

      | _ => f

  /--
  replaces calls to "this" (current module), with a call to the given module
  name.
  -/
  partial def replaceThisCalls
    (f : formula)
    (moduleName : String)
    : formula := Id.run do
    match f with
      | formula.pred_with_args p args =>
        pred_with_args
          p
          (args.map fun arg =>
            arg.replaceThisCalls moduleName)
      | formula.unaryRelBoolOperation op e =>
        formula.unaryRelBoolOperation
          op
          (e.replaceThisCalls moduleName)
      | formula.unaryLogicOperation op f =>
        formula.unaryLogicOperation
          op
          (f.replaceThisCalls moduleName)
      | formula.binaryLogicOperation op f1 f2 =>
        formula.binaryLogicOperation
          op
          (f1.replaceThisCalls moduleName)
          (f2.replaceThisCalls moduleName)
      | formula.tertiaryLogicOperation op f1 f2 f3 =>
        formula.tertiaryLogicOperation
          op
          (f1.replaceThisCalls moduleName)
          (f2.replaceThisCalls moduleName)
          (f3.replaceThisCalls moduleName)
      | formula.quantification q d n t f =>
        formula.quantification
          q
          d
          n
          (t.replaceThisCalls moduleName)
          (f.map fun f =>
            f.replaceThisCalls moduleName)

      | formula.letDeclaration name value body =>
        formula.letDeclaration
          (name)
          (value.replaceThisCalls moduleName)
          (body.map fun f => f.replaceThisCalls moduleName)

      | _ => f

  partial def getFunctionCalls
    (f : formula)
    (callableFunctions : List (commandDecl))
    (callableVariables : List (varDecl))
    : Except String
      (List (commandDecl × List (expr × List (String × List (varDecl))))) := do
      match f with
        | formula.pred_with_args _ arguments =>
          let mut functionCalls := []
          for argument in arguments do
            functionCalls :=
              functionCalls.append
                (← argument.getFunctionCalls callableFunctions callableVariables)
          return functionCalls

        | formula.unaryRelBoolOperation _ e =>
          return ← e.getFunctionCalls callableFunctions callableVariables

        | formula.unaryLogicOperation _ f =>
          f.getFunctionCalls callableFunctions callableVariables

        | formula.binaryLogicOperation _ f1 f2 =>
          let f1_cf ← f1.getFunctionCalls callableFunctions callableVariables
          let f2_cf ← f2.getFunctionCalls callableFunctions callableVariables
          return f1_cf ++ f2_cf

        | formula.tertiaryLogicOperation _ f1 f2 f3 =>
          let f1_cf ← f1.getFunctionCalls callableFunctions callableVariables
          let f2_cf ← f2.getFunctionCalls callableFunctions callableVariables
          let f3_cf ← f3.getFunctionCalls callableFunctions callableVariables
          return f1_cf ++ f2_cf ++ f3_cf

        | formula.relationComarisonOperation _ e1 e2 =>
          let e1_cf ← e1.getFunctionCalls callableFunctions callableVariables
          let e2_cf ← e2.getFunctionCalls callableFunctions callableVariables
          return e1_cf ++ e2_cf

        | formula.quantification _ _ _ te formulas =>
          let mut f_cf := []
          for f in formulas do
            f_cf :=
              f_cf.append
                (← f.getFunctionCalls callableFunctions callableVariables)

          let te_cf ← te.getFunctionCalls callableFunctions callableVariables

          return f_cf ++ te_cf

        | _ => return []

end Shared.formula
