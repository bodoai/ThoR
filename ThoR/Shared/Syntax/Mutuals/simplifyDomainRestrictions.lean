/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the mutual data structures -/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import the SymbolTable data structure -/
import ThoR.Alloy.SymbolTable.SymbolTable

/- import all independent functions for expr -/
import ThoR.Shared.Syntax.Relation.Expr.exprHelper

open Alloy
open Lean

namespace Shared
  mutual
    /--
    If possible replace domain restrictions with relations in the expr.

    This is only possible, if the relation is restricted from the
    signature it is defined in.

    E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
    -/
    partial def formula.simplifyDomainRestrictions
      (f : formula)
      (st : SymbolTable)
      : formula :=
      match f with
        | formula.bracket f => formula.bracket (f.simplifyDomainRestrictions st)

        | formula.pred_with_args p args =>
          formula.pred_with_args p (args.map fun arg => arg.simplifyDomainRestrictions st)
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

        | formula.relationComarisonOperation op expression1 expression2 =>
          formula.relationComarisonOperation
            op
            (expression1.simplifyDomainRestrictions st)
            (expression2.simplifyDomainRestrictions st)

        | formula.algebraicComparisonOperation
          op algExpression1 algExpression2 =>
          formula.algebraicComparisonOperation
            op
            (algExpression1.simplifyDomainRestrictions st)
            (algExpression2.simplifyDomainRestrictions st)

        | formula.string _ => f

    /--
    If possible replace domain restrictions with relations.

    This is only possible, if the relation is restricted from the
    signature it is defined in.

    E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
    -/
    partial def expr.simplifyDomainRestrictions
      (e : expr)
      (st : SymbolTable)
      : expr := Id.run do
      match e with
        | expr.bracket e => expr.bracket (e.simplifyDomainRestrictions st)

        | expr.binaryRelOperation operator leftSide rightSide =>
          -- needs to be domain restriction
          if !operator.isDomainRestriction then return e

          -- the right side needs to be a string for simplification
          if !rightSide.isString then return e

          let rightSideData := rightSide.getStringData
          let possibleRelations :=
            st.variableDecls.filter
              fun vd => vd.isRelation && vd.name == rightSideData

          /-
          if left and right sides are strings then it could be a call
          to a LOCAL relation
          -/
          if leftSide.isString then
            let leftSideData := leftSide.getStringData
            let matchingRelations :=
              possibleRelations.filter
                fun pr =>
                  pr.relationOf == leftSideData &&
                  !pr.isOpened

            -- if there is one matching relation use it
            if
              !matchingRelations.isEmpty &&
              !matchingRelations.length > 1
            then
              let components := [`this, leftSideData.toName, rightSideData.toName]
              let ident := mkIdent (Name.fromComponents components)
              return expr.callFromOpen (Alloy.separatedNamespace.mk ident)

          /-
          if the left side is a call to another module, then it has to
          be a relation from this module
          -/
          if !leftSide.isCallFromOpen then return e

          let leftSideData := leftSide.getCalledFromOpenData

          let leftSideComponents :=
            leftSideData.representedNamespace.getId.components

          if leftSideComponents.isEmpty then return e

          let moduleNameComponents :=
            leftSideComponents.take (leftSideComponents.length - 1)
          let moduleName :=
            (moduleNameComponents.drop 1).foldl
            (fun result component => s!"{result}_{component.toString}")
            (moduleNameComponents.get! 0).toString

          let signatureName := leftSideComponents.getLast!

          let matchingRelations :=
            possibleRelations.filter
              fun pr =>
                pr.relationOf == signatureName.toString &&
                pr.isOpened &&
                pr.openedFrom == moduleName

          -- if matching relations are not exactly one return e
          if
            matchingRelations.isEmpty ||
            matchingRelations.length > 1
          then
            return e

          let components := leftSideComponents.concat rightSideData.toName
          let ident := mkIdent (Name.fromComponents components)
          return expr.callFromOpen (Alloy.separatedNamespace.mk ident)

        | expr.dotjoin op e1 e2 =>
          expr.dotjoin
            op
            (e1.simplifyDomainRestrictions st)
            (e2.simplifyDomainRestrictions st)

        | expr.unaryRelOperation op e1 =>
          expr.unaryRelOperation
            op
            (e1.simplifyDomainRestrictions st)

        | expr.function_call_with_args functionName args =>
          expr.function_call_with_args
            functionName
            (args.map fun a => a.simplifyDomainRestrictions st)

        | expr.ifElse condition thenBody elseBody =>
          expr.ifElse
            (condition.simplifyDomainRestrictions st)
            (thenBody.simplifyDomainRestrictions st)
            (elseBody.simplifyDomainRestrictions st)

        | expr.callFromOpen _ => e
        | expr.string _ => e
        | expr.string_rb _ => e
        | expr.const _ => e

    /--
    If possible replace domain restrictions with relations.

    This is only possible, if the relation is restricted from the
    signature it is defined in.

    E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
    -/
    partial def typeExpr.simplifyDomainRestrictions
      (te : typeExpr)
      (st : SymbolTable)
      : typeExpr :=
        match te with
          | typeExpr.arrowExpr ae =>
            typeExpr.arrowExpr (ae.simplifyDomainRestrictions st)
          | typeExpr.multExpr m e =>
            typeExpr.multExpr m (e.simplifyDomainRestrictions st)
          | typeExpr.relExpr e =>
            typeExpr.relExpr (e.simplifyDomainRestrictions st)

    /--
    If possible replace domain restrictions with relations.

    This is only possible, if the relation is restricted from the
    signature it is defined in.

    E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
    -/
    partial def algExpr.simplifyDomainRestrictions
      (ae : algExpr)
      (st : SymbolTable)
      : algExpr :=
        match ae with
          | algExpr.number _ => ae
          | algExpr.binaryAlgebraOperation op ae1 ae2 =>
            algExpr.binaryAlgebraOperation
              op
              (ae1.simplifyDomainRestrictions st)
              (ae2.simplifyDomainRestrictions st)

          | algExpr.unaryAlgebraOperation op ae =>
            algExpr.unaryAlgebraOperation
              op
              (ae.simplifyDomainRestrictions st)

          | algExpr.cardExpression e =>
            algExpr.cardExpression (e.simplifyDomainRestrictions st)

    /--
    If possible replace domain restrictions with relations.

    This is only possible, if the relation is restricted from the
    signature it is defined in.

    E.g. m1/a<:r gets simplified to the relation r IF r is a relation of a
    -/
    partial def arrowOp.simplifyDomainRestrictions
      (ao : arrowOp)
      (st : SymbolTable)
      : arrowOp :=
        match ao with
          | arrowOp.multArrowOpExpr e1 m1 m2 e2 =>
            arrowOp.multArrowOpExpr
              (e1.simplifyDomainRestrictions st)
              m1 m2
              (e2.simplifyDomainRestrictions st)

          | arrowOp.multArrowOpExprLeft e1 m1 m2 ae2 =>
            arrowOp.multArrowOpExprLeft
              (e1.simplifyDomainRestrictions st)
              m1 m2
              (ae2.simplifyDomainRestrictions st)

          | arrowOp.multArrowOpExprRight ae1 m1 m2 e2 =>
            arrowOp.multArrowOpExprRight
              (ae1.simplifyDomainRestrictions st)
              m1 m2
              (e2.simplifyDomainRestrictions st)

          | arrowOp.multArrowOp ae1 m1 m2 ae2 =>
            arrowOp.multArrowOp
              (ae1.simplifyDomainRestrictions st)
              m1 m2
              (ae2.simplifyDomainRestrictions st)

  end
end Shared
