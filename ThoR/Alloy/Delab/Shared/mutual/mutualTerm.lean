/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Semantics.Semantics
import ThoR.Relation.Set
import ThoR.Alloy.Elab.BlocklessAlloy.blocklessAlloy

/- import of the syntax for expr -/
import ThoR.Shared.Syntax.Relation.Expr.expr

/- import of the syntax for algExpr -/
import ThoR.Shared.Syntax.Algebra.AlgExpr.algExpr

/- import of the syntax for typeExpr -/
import ThoR.Shared.Syntax.TypeExpr.typeExpr

/- import of the syntax for formula -/
import ThoR.Shared.Syntax.Formula.formula

import ThoR.Alloy.UnhygienicUnfolder

open Lean PrettyPrinter Delaborator SubExpr

open Shared


@[app_unexpander ThoR.Semantics.Term.local_rel_var]
def unexpTerm_local_rel_var : Unexpander
  | `($_ $value:ident) => do
    let e := unhygienicUnfolder
      `(expr_without_if | $value:ident)
    let bb := unhygienicUnfolder
      `(blockless_body | $e:expr_without_if)

    `([alloy | $bb:blockless_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.global_rel_var]
def unexpTerm_global_rel_var : Unexpander
  | `($_ $_:ident $name:str) => do
    let e := unhygienicUnfolder
      `(expr_without_if| $(mkIdent name.getString.toName):ident)

    let bb := unhygienicUnfolder
      `(blockless_body | $e:expr_without_if)

    `([alloy | $bb:blockless_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.eq]
def unexpTerm_eq : Unexpander
  | `($_ $param1 $param2) => do
    `($param1 = $param2)
    /-
    let leftSide := unexpExpressionWithoutIfTerm param1
    let rightSide := unexpExpressionWithoutIfTerm param2
    let formula_body := unhygienicUnfolder
      `(formula | $leftSide:expr_without_if = $rightSide:expr_without_if)

    `([ alloy | $formula_body:formula ])
    -/

  | _ => throw Unit.unit

-- TODO: Add pred declaration to blockless and add it here?
-- Blockless Preddeclaration? Usage of variables like in blockless formula?
@[app_unexpander ThoR.Semantics.Term.pred_def]
def unexpTerm_predDef : Unexpander
  | `($_ $name $param) => do

    let nn := match name with
      | `(term | $n:str) => n.getString
      | _ => unreachable!

    match param with
      -- TODO: This has to be executed as many times as there is a match to lam ...
      | `(ThoR.Semantics.Term.lam $lambda_function) =>
        match lambda_function with
          | `(fun $lambda_variable ↦ $body) =>
            match lambda_variable with
              | `(Lean.Parser.Term.funBinder | $(variable_nameTerm):term) =>
                match variable_nameTerm with
                  -- TODO: Blockless pred decl is needed to correctly display this, currently := pred p1 x (x = x)
                  | `(term| $variable_name:ident) =>
                    `( $(mkIdent `pred)
                        $(mkIdent nn.toName)
                        $(variable_name)
                        ($(body))
                      )
                  | _ =>`($(mkIdent `pred) $(mkIdent nn.toName))
          | _ => `($(mkIdent `pred) $(mkIdent nn.toName) $lambda_function)

      | _ =>  `($(mkIdent `pred) $(mkIdent nn.toName) $param)

  | _ => throw Unit.unit
