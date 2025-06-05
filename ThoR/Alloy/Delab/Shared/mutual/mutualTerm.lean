/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Semantics.Semantics
import ThoR.Alloy.Delab.DelaborationAlloySyntax

import ThoR.Alloy.UnhygienicUnfolder

open Lean PrettyPrinter Delaborator SubExpr

open Shared


@[app_unexpander ThoR.Semantics.Term.local_rel_var]
def unexpTerm_local_rel_var : Unexpander
  | `($_ $value) => do

    let value_ident :=
      match value with
        |`(ident | $value_ident:ident) => value_ident
        | _ => unreachable!

    let bb := unhygienicUnfolder
      `(delaborator_body | $value_ident:ident )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.global_rel_var]
def unexpTerm_global_rel_var : Unexpander
  | `($_ $_:ident $name:str) => do
    let name_ident := mkIdent name.getString.toName

    let bb := unhygienicUnfolder
      `(delaborator_body | $name_ident:ident )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.eq]
def unexpTerm_eq : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body = $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.union]
def unexpTerm_union : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body + $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.lam]
def unexp_lam : Unexpander
  | `($_ $lambda_function) =>
    match lambda_function with
      | `(fun $lambda_variable ↦ [alloy' | $body ]) =>
        match lambda_variable with
          | `(Lean.Parser.Term.funBinder | $(variable_nameTerm):term) =>
            match variable_nameTerm with
              | `(term| $variable_name:ident) =>
                let bb :=
                  unhygienicUnfolder
                  `(delaborator_body |
                    $variable_name:ident
                    { $body:delaborator_body }
                  )

                `(
                    [ alloy' | $bb:delaborator_body ]
                  )

              | _ => throw Unit.unit
      | _ => throw Unit.unit
  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.pred_def]
def unexpTerm_predDef : Unexpander
  | `($_ $name [alloy' | $body] ) => do

    let nn := match name with
      | `(term | $n:str) => n.getString
      | _ => unreachable!

    let bb := unhygienicUnfolder
      `( delaborator_body |
        pred
        $(mkIdent nn.toName)
        $body
      )

    `([alloy' | $bb:delaborator_body])

  | _ => throw Unit.unit
