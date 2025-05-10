/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

import ThoR.Alloy.UnhygienicUnfolder
import ThoR.Alloy.Syntax.AlloyData.alloyData
import ThoR.Alloy.Config

import ThoR.Relation.ElabCallMacro
import ThoR.Relation.Quantification

import Lean

open Lean
open ThoR Quantification Alloy Config

namespace Shared

  mutual

    /--
    Generates a Lean term corosponding to the type expr (unrelated to a block)
    -/
    partial def expr.toTermOutsideBlock
      (e : expr)
      (availableAlloyData : List (alloyData) := [])
      (localContextUserNames : List Name := [])
      : Except String Term := do
        match e with
          | expr.const c =>
            return (c.toTerm)

          | expr.string s => do

            /-
            check if the name is defined in the existing modules, but only
            if the name is not defined in a variable definition
            -/
            if !(localContextUserNames.contains s.toName) then
              let mut possibleVarDecls := []
              for alloyData in availableAlloyData do
                let possibleMatches :=
                  alloyData.st.variableDecls.filter fun vd => vd.name == s

                if !possibleMatches.isEmpty then
                  possibleVarDecls := possibleVarDecls.concat
                    (alloyData.st.name, possibleMatches)

              if !possibleVarDecls.isEmpty then
                if
                  -- if there are matches in more than one module
                  possibleVarDecls.length > 1 ||
                  /-
                    or more than one match in a module
                    (this should be impossible)
                  -/
                  possibleVarDecls.any fun pv => pv.2.length > 1
                then
                  throw s!"The call to {s} is ambiguous. \
                  There are multiple declared variables \
                  which it could refer to ({possibleVarDecls})"

                let calledVarDecl := possibleVarDecls.get! 0
                let calledBlockName := calledVarDecl.1
                let callNameComponents := [calledBlockName, `vars, s.toName]
                let callName := Name.fromComponents callNameComponents
                return unhygienicUnfolder
                  `((@$(mkIdent callName) $(baseType.ident) _ _))

            return unhygienicUnfolder `($(mkIdent s.toName))

          | expr.callFromOpen sn =>
            return sn.toTerm

          | expr.function_call_with_args called_function arguments =>
            let mut argumentsTerm
              ← (arguments.get! 0).toTermOutsideBlock

            for arg in arguments.drop 1 do
              let argTerm ← arg.toTermOutsideBlock
              argumentsTerm :=
                unhygienicUnfolder
                  `(argumentsTerm $argTerm)

            let function_name_components := []

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
            let eTerm ← e.toTermOutsideBlock
              availableAlloyData localContextUserNames

            return unhygienicUnfolder `(( $(op.toTerm)
                $(eTerm)
              ))

          | expr.binaryRelOperation op e1 e2 =>
            let e1Term ← e1.toTermOutsideBlock
              availableAlloyData localContextUserNames
            let e2Term ← e2.toTermOutsideBlock
              availableAlloyData localContextUserNames
            return unhygienicUnfolder `(( $(op.toTerm)
                $(e1Term)
                $(e2Term)
              ))

          | expr.dotjoin dj e1 e2 =>
            let e1Term ← e1.toTermOutsideBlock
              availableAlloyData localContextUserNames
            let e2Term ← e2.toTermOutsideBlock
              availableAlloyData localContextUserNames
            return unhygienicUnfolder `(( $(dj.toTerm)
                $(e1Term)
                $(e2Term)
              ))

          | expr.ifElse condition thenBody elseBody =>
            let conditionTerm ← condition.toTermOutsideBlock
               availableAlloyData localContextUserNames

            let thenBodyTerm ← thenBody.toTermOutsideBlock
              availableAlloyData localContextUserNames

            let elseBodyTerm ← elseBody.toTermOutsideBlock
              availableAlloyData localContextUserNames

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
    Generates a Lean term corosponding to the type formula (unrelated to a block)
    -/
    partial def formula.toTermOutsideBlock
      (f : formula)
      (availableAlloyData : List (alloyData) := [])
      (localContextUserNames : List Name := [])
      : Except String ((Term)) := do
      match f with
        | formula.string s => do
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
            `(
              (
                $(op.toTerm)
                $(← algE1.toTermOutsideBlock)
                $(← algE2.toTermOutsideBlock)
              )
            )

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
          let firstForm := f.get! 0
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
                fun ( $(names.get! 0) : $(← te.toTermOutsideBlock))
                  => $(unhygienicUnfolder completefTerm)))

          -- multiple parameter is Group constructor
          else
            let mut formulaGroup :=
              `(($(mkIdent ``Group.var) (
                fun ( $(names.get! 0) : $(← te.toTermOutsideBlock))
                  => $(mkIdent ``Group.formula) $(unhygienicUnfolder completefTerm))))
            for n in (names.drop 1) do
              formulaGroup :=
                `(($(mkIdent ``Group.var) (
                  fun ( $(n) : $(← te.toTermOutsideBlock))
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

          let mut bodyTerm := unhygienicUnfolder `(term | ($(bodyTermList.get! 0)))
          for elem in bodyTermList do
            bodyTerm := unhygienicUnfolder `(bodyTerm ∧ ($(elem)))

          let letTerm := unhygienicUnfolder `(let $(nameT):ident := $(valueT):term; $(bodyTerm))

          return letTerm

    /--
    Generates a Lean term corosponding to the type typeExpr (unrelated to a block)
    -/
    partial def typeExpr.toTermOutsideBlock
      (te : typeExpr)
      : Except String Term := do
        match te with
          | Shared.typeExpr.arrowExpr ae =>
            return unhygienicUnfolder
              `($(mkIdent ``ThoR.Rel) $(← ae.toTermOutsideBlock))

          | Shared.typeExpr.multExpr m e =>
            return unhygienicUnfolder
              `($(mkIdent ``ThoR.Rel)
                ($(mkIdent ``RelType.mk.unary_rel)
                  $(m.toTerm) $(← e.toTermOutsideBlock)))

          | Shared.typeExpr.relExpr e =>
            return unhygienicUnfolder
              `($(mkIdent ``ThoR.Rel)
                ($(mkIdent ``RelType.mk.rel)
                  $(← e.toTermOutsideBlock)))

    /--
    Generates a Lean term corosponding to the type algExpr (unrelated to a block)
    -/
    partial def algExpr.toTermOutsideBlock
      (ae : algExpr)
      : Except String Term := do
        match ae with
          | algExpr.number n =>
            return unhygienicUnfolder
              `($(Lean.Syntax.mkNumLit s!"{n.natAbs}"):num)

          | algExpr.cardExpression e =>
            let eTerm ← e.toTermOutsideBlock
            return unhygienicUnfolder
              `(($(mkIdent ``ThoR.Card.card) $(eTerm)))

          | algExpr.unaryAlgebraOperation op ae =>
            let aeTerm ← ae.toTermOutsideBlock
            return unhygienicUnfolder
              `(($(op.toTerm) $(aeTerm)))

          | algExpr.binaryAlgebraOperation op ae1 ae2 =>
            let ae1Term ← ae1.toTermOutsideBlock
            let ae2Term ← ae2.toTermOutsideBlock
            return unhygienicUnfolder
              `(($(op.toTerm) $(ae1Term) $(ae2Term)))

    /--
    Generates a Lean term corosponding to the type algExpr (unrelated to a block)
    -/
    partial def arrowOp.toTermOutsideBlock
      (ao : arrowOp)
      : Except String Term := do

      match ao with
        | arrowOp.multArrowOpExpr
            (e1 : expr)
            (m1 : mult)
            (m2 : mult)
            (e2 : expr) =>
              let e1Term ← e1.toTermOutsideBlock
              let e2Term ← e2.toTermOutsideBlock
              return unhygienicUnfolder
                `(
                  $(mkIdent ``RelType.complex)
                    ($(mkIdent ``ThoR.Rel.getType) ($(e1Term)))
                    ($(m1.toTerm))
                    ($(m2.toTerm))
                    ($(mkIdent ``ThoR.Rel.getType) ($(e2Term)))
                )

        | arrowOp.multArrowOpExprLeft
            (e1 : expr)
            (m1 : mult)
            (m2 : mult)
            (ae2 : arrowOp) =>
              let e1Term ← e1.toTermOutsideBlock
              let ae2Term ← ae2.toTermOutsideBlock
              return unhygienicUnfolder
                `(
                  $(mkIdent ``RelType.complex)
                    ($(mkIdent ``ThoR.Rel.getType) ($(e1Term)))
                    ($(m1.toTerm))
                    ($(m2.toTerm))
                    $(ae2Term)
                )

        | arrowOp.multArrowOpExprRight
            (ae1 : arrowOp)
            (m1 : mult)
            (m2 : mult)
            (e2 : expr) =>
              let ae1Term ← ae1.toTermOutsideBlock
              let e2Term ← e2.toTermOutsideBlock
              return unhygienicUnfolder
                `(
                  $(mkIdent ``RelType.complex)
                    $(ae1Term)
                    ($(m1.toTerm))
                    ($(m2.toTerm))
                    ($(mkIdent ``ThoR.Rel.getType) ($(e2Term)))
                )

        | arrowOp.multArrowOp
            (ae1 : arrowOp)
            (m1 : mult)
            (m2 : mult)
            (ae2 : arrowOp) =>
              let ae1Term ← ae1.toTermOutsideBlock
              let ae2Term ← ae2.toTermOutsideBlock
              return unhygienicUnfolder
                `(
                  $(mkIdent ``RelType.complex)
                    $(ae1Term)
                    ($(m1.toTerm))
                    ($(m2.toTerm))
                    $(ae2Term)
                )

  end

end Shared
