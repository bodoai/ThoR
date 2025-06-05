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

/-
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
-/

private partial def getArgs
  (body : TSyntax `term)
  : (Array (TSyntax `delaborator_body)) × (TSyntax `delaborator_body) := Id.run do
  let mut result := #[]
  let mut trueBody := unhygienicUnfolder `(delaborator_body|$(mkIdent `default):ident)
  match body with
    | `(ThoR.Semantics.Term.lam $lambda_function) =>
      match lambda_function with
        | `(fun $lambda_variable ↦ $body) =>
          match lambda_variable with
            | `( Lean.Parser.Term.funBinder |
                $(variable_nameTerm):term ) =>
                  match variable_nameTerm with
                    | `($variable_name:ident) =>
                      let arg := unhygienicUnfolder `(delaborator_body|$variable_name:ident)
                      result := result.push arg
                    | _ => result := result

          /- if the body is not a lam then its the final body -/
          match body with
            | `([alloy'| $body]) =>
              trueBody := body
            | _ =>
              let subResult := (getArgs body)
              result := result.append subResult.1
              trueBody := subResult.2

        | _ => result := result
    | _ => result := result

  (result, trueBody)

@[app_unexpander ThoR.Semantics.Term.pred_def]
def unexpTerm_predDef : Unexpander
  | `($_ $name $body ) => do

    let nn := match name with
      | `(term | $n:str) => n.getString
      | _ => unreachable!

    --panic! s!"{body}"

    /-get args here to group them-/
    let argsAndBody := getArgs body
    let args := argsAndBody.1
    let argsBody := unhygienicUnfolder `(delaborator_body | [$[$(args)],*])
    let body := unhygienicUnfolder `(delaborator_body | { $(argsAndBody.2) } )

    let bb :=
      if args.isEmpty then
        unhygienicUnfolder
        `( delaborator_body |
          pred
          $(mkIdent nn.toName)
          $body
        )
      else
        unhygienicUnfolder
          `( delaborator_body |
            pred
            $(mkIdent nn.toName)
            $argsBody
            $body
          )

    `([alloy' | $bb:delaborator_body])

  | _ => throw Unit.unit
