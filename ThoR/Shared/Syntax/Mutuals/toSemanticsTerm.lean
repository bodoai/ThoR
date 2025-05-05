/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import needed functions -/
import ThoR.Shared.Syntax.Mutuals.getCalledVariables
import ThoR.Shared.Syntax.Mutuals.toStringRb

/- import the Semantics to be used (in the resulting Term) -/
import ThoR.Semantics.Semantics

import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.Config

import ThoR.Relation.ElabCallMacro
import ThoR.Relation.Quantification

open Lean
open ThoR Quantification Alloy Config

namespace Shared

  mutual

    /--
    Generates a Lean term corosponding to the type expr
    -/
    partial def expr.toSemanticsTerm
      (e : expr)
      (blockName : Name)
      (variableNames : List (String)) -- to check if var or pred
      (callableVariables : List (varDecl))
      (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
      -- used to know which names must be pure
      (pureNames : List (String) := [])
      : Except String Term := do
        match e with
          | expr.const c =>
            return (c.toTerm)

          | expr.string s => do

            if !(pureNames.contains s) then
              return unhygienicUnfolder `(
                $(mkIdent ``ThoR.Semantics.Expression.rel)
                (∻ $(mkIdent s!"{blockName}.vars.{s}".toName))
              )

            return unhygienicUnfolder `(
                $(mkIdent ``ThoR.Semantics.Expression.rel)
                $(mkIdent s.toName)
              )

          | expr.callFromOpen sn =>
            let snt := sn.representedNamespace.getId.toString
            return unhygienicUnfolder `((
              ∻ $(mkIdent s!"{blockName}.vars.{snt}".toName)
            ))

          | expr.function_call_with_args called_function arguments =>
            let mut argumentsTerm
              ← (arguments.get! 0).toSemanticsTerm blockName
                variableNames callableVariables callablePredicates pureNames

            for arg in arguments.drop 1 do
              let argTerm ← arg.toSemanticsTerm blockName
                variableNames callableVariables callablePredicates pureNames

              argumentsTerm :=
                unhygienicUnfolder
                  `(argumentsTerm $argTerm)

            let function_name_components := [blockName, `funs]

            let basic_function_name := called_function.toName

            let function_name :=
              Name.fromComponents
                (function_name_components.concat basic_function_name)

            return unhygienicUnfolder
              `(
                (
                  ∻ $(mkIdent function_name)
                ) $argumentsTerm
              )

          | expr.unaryRelOperation op e =>
            let eTerm ← e.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder `(( $(op.toTerm)
                $(eTerm)
              ))

          | expr.binaryRelOperation op e1 e2 =>
            let e1Term ← e1.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            let e2Term ← e2.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder `(( $(op.toTerm)
                $(e1Term)
                $(e2Term)
              ))

          | expr.dotjoin dj e1 e2 =>
            let e1Term ← e1.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            let e2Term ← e2.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder `(( $(dj.toTerm)
                $(e1Term)
                $(e2Term)
              ))

          | expr.ifElse condition thenBody elseBody =>
            let conditionTerm ← condition.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            let thenBodyTerm ← thenBody.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            let elseBodyTerm ← elseBody.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder
              `(
                $(conditionTerm) -> $(thenBodyTerm)
                ∧
                (Not $(conditionTerm)) → $(elseBodyTerm)
              )

          | expr.string_rb s => do
            return unhygienicUnfolder
              `((@$(mkIdent s.toName) $(baseType.ident) _ _))

    /--
    Generates a Lean term corosponding to the type formula
    -/
    partial def formula.toSemanticsTerm
      (f: formula)
      (blockName : Name)
      (variableNames : List (String)) -- to check if var or pred
      (callableVariables : List (varDecl))
      (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
      -- names that have to be pure with no namespace (quantors and args)
      (pureNames : List (String) := [])
      : Except String Term := do

        match f with
        | formula.string s => do
          -- Quantors and args dont use namespaces
          if pureNames.contains s then
            return unhygienicUnfolder `($(mkIdent s.toName))

          else
            -- check if the ident is a variable or def
            if variableNames.contains s then
              return unhygienicUnfolder
                `((
                  ∻ $(mkIdent s!"{blockName}.vars.{s}".toName)
                ))

            else
              return unhygienicUnfolder
                `((
                  ∻ $(mkIdent s!"{blockName}.preds.{s}".toName)
                ))

        | formula.pred_with_args p pa => do
          let mut term := unhygienicUnfolder
            `((
                ∻ $(mkIdent s!"{blockName}.preds.{p}".toName)
              ))

          let possibleCalledPredicates :=
            (callablePredicates.filter fun cp => cp.1.name == p)

          if possibleCalledPredicates.isEmpty || possibleCalledPredicates.length > 1 then
            panic!
              s!"Called Preds is Empty or more than one \
              in formulaService {possibleCalledPredicates}"

          let calledPredicate := possibleCalledPredicates.get! 0

          let calledArgsVarDecls :=
            (calledPredicate.1.predArgs.map fun cp =>
              cp.1.names.map fun _ =>
                cp.2).join

          for index in [0:pa.length] do

            --let definedArg := calledPredArgs.get! index

            let vd := calledArgsVarDecls.get! index

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

            let calledArg := pa.get! index
            let calledVarDecls_of_arg_to_cast ←
              calledArg.getCalledVariables callableVariables

            let calledVarDecls_of_arg_to_cast_joined :=
              (calledVarDecls_of_arg_to_cast.map fun a => a.2).join

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
                let cv := (calledVarDecls_of_arg_to_cast_joined.get! 0)
                cv.type.toString == typeReplacementName
              )

            let calledArgTerm ← calledArg.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            if
              cast_type_as_expr_string == calledArg ||
              cast_type_as_expr_string_rb == calledArg ||
              cast_type_equals_called_var_type
            then


              term :=
                unhygienicUnfolder `(term | $(term):term $(calledArgTerm):term)

            else

              let cast_type_term ← cast_type_as_type_expr_relExpr.toSemanticsTerm
                blockName variableNames callableVariables
                callablePredicates pureNames

              let castCommand : Term :=
                unhygienicUnfolder
                  `(term |
                    cast
                    ($calledArgTerm:term)
                    $(cast_type_term):term)

              term :=
                unhygienicUnfolder
                  `(term |
                    $(term)
                    $(castCommand)
                  )

          return term

        | formula.unaryRelBoolOperation op e =>
          return unhygienicUnfolder
            `(
              (
                $(op.toTerm)
                $(← e.toSemanticsTerm
                  blockName variableNames callableVariables
                  callablePredicates pureNames)
              )
            )

        | formula.unaryLogicOperation op f =>
          let fTerm ← f.toSemanticsTerm blockName variableNames
            callableVariables callablePredicates pureNames

          return unhygienicUnfolder `(term | ( $(op.toTerm) $(fTerm)))

        | formula.binaryLogicOperation op f1 f2 =>
          let f1Term ←
            f1.toSemanticsTerm blockName variableNames
              callableVariables callablePredicates pureNames

          let f2Term ←
            f2.toSemanticsTerm blockName variableNames
              callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(
              ( $(op.toTerm)
                $(f1Term)
                $(f2Term)
              )
            )

        | formula.tertiaryLogicOperation op f1 f2 f3 =>
          let f1Term ←
            f1.toSemanticsTerm blockName variableNames
              callableVariables callablePredicates pureNames

          let f2Term ←
            f2.toSemanticsTerm blockName variableNames
              callableVariables callablePredicates pureNames

          let f3Term ←
            f3.toSemanticsTerm blockName variableNames
              callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(
              ( $(op.toTerm)
                $(f1Term)
                $(f2Term)
                $(f3Term)
              )
            )

        | formula.algebraicComparisonOperation op ae1 ae2 =>
          return unhygienicUnfolder
            `(
              (
                $(op.toTerm)
                $(← ae1.toSemanticsTerm blockName variableNames callableVariables
                  callablePredicates pureNames)
                $(← ae2.toSemanticsTerm blockName variableNames callableVariables
                  callablePredicates pureNames)
              )
            )

        | formula.relationComarisonOperation op e1 e2 =>
          let e1Term ← e1.toSemanticsTerm
            blockName variableNames callableVariables
              callablePredicates pureNames

          let e2Term ← e2.toSemanticsTerm
            blockName variableNames callableVariables
              callablePredicates pureNames

          return unhygienicUnfolder
            `(
              ( $(op.toTerm)
                $(e1Term)
                $(e2Term)
              )
            )

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
          let firstForm := f.get! 0
          let firstFTerm ←
            firstForm.toSemanticsTerm
              blockName variableNames (callableVariables ++ quantVarDecls) callablePredicates
              (pureNames.append n)

          let mut completefTerm : Term :=
            unhygienicUnfolder `(term | $(firstFTerm))

          for form in f.drop 1 do
            let fTerm ←
              form.toSemanticsTerm
                blockName variableNames (callableVariables ++ quantVarDecls) callablePredicates
                (pureNames.append n)

            completefTerm :=
              unhygienicUnfolder `(( $(completefTerm) ∧
                  ($(fTerm))
                ))

          completefTerm :=
            unhygienicUnfolder `((
              $(mkIdent ``Formula.prop)
              ($(completefTerm))
              ))

          -- singular parameter is var constructor
          if names.length == 1 then
              return unhygienicUnfolder `(($(mkIdent ``Formula.var) $(q.toTerm)) (
                fun ( $(names.get! 0) : $(← te.toSemanticsTerm blockName variableNames callableVariables callablePredicates pureNames))
                  => $(completefTerm)))

          -- multiple parameter is Group constructor
          else
            let mut formulaGroup : Term := unhygienicUnfolder
              `(($(mkIdent ``Group.var) (
                fun ( $(names.get! 0) : $(← te.toSemanticsTerm blockName variableNames callableVariables callablePredicates pureNames))
                  => $(mkIdent ``Group.formula) $(completefTerm))))
            for n in (names.drop 1) do
              formulaGroup := unhygienicUnfolder
                `(($(mkIdent ``Group.var) (
                  fun ( $(n) : $(← te.toSemanticsTerm blockName variableNames callableVariables callablePredicates pureNames))
                    => $(formulaGroup))))
            if disjunction then
              formulaGroup := unhygienicUnfolder
                `(( $(mkIdent ``Formula.disj)
                    $(mkIdent ``Shared.quant.all)
                    $(formulaGroup)
                  ))
            else
              formulaGroup := unhygienicUnfolder
                `(( $(mkIdent ``Formula.group)
                    $(mkIdent ``Shared.quant.all)
                    $(formulaGroup)
                  ))

            return formulaGroup

        | formula.letDeclaration name value body =>
          let nameT := mkIdent name
          let valueT ← value.toSemanticsTerm blockName variableNames callableVariables callablePredicates
          let e_bodyT :=
            (body.map fun e =>
              e.toSemanticsTerm blockName variableNames callableVariables callablePredicates
              )
          let mut bodyTermList : List Term := []
          for elem in e_bodyT do
            match elem with
              | Except.error msg => throw msg
              | Except.ok data => bodyTermList := bodyTermList.concat (data)


          if bodyTermList.isEmpty then throw s!"let {name}={value} has empty body"

          let mut bodyTerm := `(term | ($(bodyTermList.get! 0)))
          for elem in bodyTermList do
            bodyTerm := `(bodyTerm ∧ ($(elem)))

          let letTerm : Term := unhygienicUnfolder
            `(let $(nameT):ident := $(valueT):term; $(unhygienicUnfolder bodyTerm))

          return letTerm

    /--
    Generates a Lean term corosponding to the type typeExpr
    -/
    partial def typeExpr.toSemanticsTerm
      (te : typeExpr)
      (blockName : Name)
      (variableNames : List (String)) -- to check if var or pred
      (callableVariables : List (varDecl))
      (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
      -- names that have to be pure with no namespace (quantors and args)
      (pureNames : List (String) := [])
      : Except String Term := do
        match te with
          | Shared.typeExpr.arrowExpr ae =>
            let aeTerm ← ae.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder
              `($(mkIdent ``ThoR.Rel) $(aeTerm))

          | Shared.typeExpr.multExpr m e =>
            let eTerm ← e.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder
              `($(mkIdent ``ThoR.Rel)
                ($(mkIdent ``RelType.mk.unary_rel)
                  $(m.toTerm) $(eTerm)))

          | Shared.typeExpr.relExpr e =>
            let eTerm ← e.toSemanticsTerm blockName
              variableNames callableVariables callablePredicates pureNames

            return unhygienicUnfolder
              `($(mkIdent ``ThoR.Rel)
                ($(mkIdent ``RelType.mk.rel) $(eTerm)))

    /--
    Generates a Lean term corosponding to the type arrowOp
    -/
    partial def arrowOp.toSemanticsTerm
      (ao : arrowOp)
      (blockName : Name)
      (variableNames : List (String)) -- to check if var or pred
      (callableVariables : List (varDecl))
      (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
      -- names that have to be pure with no namespace (quantors and args)
      (pureNames : List (String) := [])
      : Except String Term := do

      match ao with
        | arrowOp.multArrowOpExpr
          (e1 : expr) (m1 : mult) (m2 : mult) (e2 : expr) =>
          let e1Term ← e1.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          let e2Term ← e2.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(
              $(mkIdent ``RelType.complex)
                ($(mkIdent ``ThoR.Rel.getType) ($(e1Term)))
                ($(m1.toTerm))
                ($(m2.toTerm))
                ($(mkIdent ``ThoR.Rel.getType) ($(e2Term)))
          )
        | arrowOp.multArrowOpExprLeft (e1 : expr) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
          let e1Term ← e1.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          let ae2Term ← ae2.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(
              $(mkIdent ``RelType.complex)
                ($(mkIdent ``ThoR.Rel.getType) ($(e1Term)))
                ($(m1.toTerm))
                ($(m2.toTerm))
                $(ae2Term)
          )

        | arrowOp.multArrowOpExprRight (ae1 : arrowOp) (m1 : mult) (m2 : mult) (e2 : expr) =>
          let ae1Term ← ae1.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          let e2Term ← e2.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(
              $(mkIdent ``RelType.complex)
                $(ae1Term)
                ($(m1.toTerm))
                ($(m2.toTerm))
                ($(mkIdent ``ThoR.Rel.getType) ($(e2Term)))
            )

        | arrowOp.multArrowOp (ae1 : arrowOp) (m1 : mult) (m2 : mult) (ae2 : arrowOp) =>
          let ae1Term ← ae1.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          let ae2Term ← ae2.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(
              $(mkIdent ``RelType.complex)
                $(ae1Term)
                ($(m1.toTerm))
                ($(m2.toTerm))
                $(ae2Term)
            )

    /--
    Generates a Lean term corosponding with the type
    -/
    partial def algExpr.toSemanticsTerm
    (ae : algExpr)
    (blockName : Name)
    (variableNames : List (String)) -- to check if var or pred
    (callableVariables : List (varDecl))
    (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
    -- names that have to be pure with no namespace (quantors and args)
    (pureNames : List (String) := [])
    : Except String Term := do
      match ae with
        | algExpr.number n =>
          return unhygienicUnfolder
            `($(Lean.Syntax.mkNumLit s!"{n.natAbs}"):num)

        | algExpr.cardExpression e =>
          let eTerm ← e.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(($(mkIdent ``ThoR.Card.card) $(eTerm)))

        | algExpr.unaryAlgebraOperation op ae =>
          let aeTerm ← ae.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(($(op.toTerm) $(aeTerm)))

        | algExpr.binaryAlgebraOperation op ae1 ae2 =>
          let ae1Term ← ae1.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          let ae2Term ← ae2.toSemanticsTerm blockName
            variableNames callableVariables callablePredicates pureNames

          return unhygienicUnfolder
            `(($(op.toTerm) $(ae1Term) $(ae2Term)))

  end

end Shared
