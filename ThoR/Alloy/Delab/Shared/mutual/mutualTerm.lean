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


@[app_unexpander ThoR.Semantics.ExpressionTerm.local_rel_var]
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

@[app_unexpander ThoR.Semantics.ExpressionTerm.global_rel_var]
def unexpTerm_global_rel_var : Unexpander
  | `($_ $_:ident $name:str) => do
    let name_ident := mkIdent name.getString.toName

    let bb := unhygienicUnfolder
      `(delaborator_body | $name_ident:ident )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.union]
def unexpTerm_union : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body + $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.intersect]
def unexpTerm_intersection : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body & $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.difference]
def unexpTerm_difference : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body - $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.overwrite]
def unexpTerm_overwrite : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body ++ $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.domain_restriction]
def unexpTerm_domain_restriction : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body <: $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.range_restriction]
def unexpTerm_range_restriction : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body :> $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.dotjoin]
def unexpTerm_dotjoin : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body . $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.transclos]
def unexpTerm_transclos : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | ^ $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.reflexive_closure]
def unexpTerm_reflexive_closure : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | * $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.transposition]
def unexpTerm_transposition : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | ~ $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

/- expr if else-/
@[app_unexpander ThoR.Semantics.ExpressionTerm.if_then_else]
def unexpTerm_if_then_else : Unexpander
  | `($_ [alloy'|$condition] [alloy'|$thenBody] [alloy'|$elseBody] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |
        $condition:delaborator_body =>
        $thenBody:delaborator_body else
        $elseBody:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.bracket]
def unexpTerm_bracket : Unexpander
  | `($_ [alloy'| $body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |  ($body:delaborator_body ))

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

@[app_unexpander ThoR.Semantics.Term.fun_def]
def unexpTerm_fun_def : Unexpander
  | `($_ $name $body ) => do

    let nn := match name with
      | `(term | $n:str) => n.getString
      | _ => unreachable!

    /-get args here to group them-/
    let argsAndBody := getArgs body
    let args := argsAndBody.1
    let argsBody := unhygienicUnfolder `(delaborator_body | [$[$(args)],*])
    let body := unhygienicUnfolder `(delaborator_body | { $(argsAndBody.2) } )

    let bb :=
      if args.isEmpty then
        unhygienicUnfolder
        `( delaborator_body |
          fun
          $(mkIdent nn.toName)
          $body
        )
      else
        unhygienicUnfolder
          `( delaborator_body |
            fun
            $(mkIdent nn.toName)
            $argsBody
            $body
          )

    `([alloy' | $bb:delaborator_body])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.number]
def unexpTerm_number : Unexpander
  | `($_ $value ) => do

    let value_NumLit :=
      match value with
        |`(num | $value_NumLit:num) => value_NumLit
        | _ => unreachable!

    let bb := unhygienicUnfolder
      `(delaborator_body | $value_NumLit:num )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.negation]
def unexpTerm_negation : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | - $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.add]
def unexpTerm_add : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | plus[$param1:delaborator_body, $param2:delaborator_body] )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.sub]
def unexpTerm_sub : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | minus[$param1:delaborator_body, $param2:delaborator_body] )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.mul]
def unexpTerm_mul : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | mul[$param1:delaborator_body, $param2:delaborator_body] )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.div]
def unexpTerm_div : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | div[$param1:delaborator_body, $param2:delaborator_body] )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.rem]
def unexpTerm_rem : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | rem[$param1:delaborator_body, $param2:delaborator_body] )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.AlgebraTerm.card]
def unexpTerm_card : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | #$body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.no]
def unexpTerm_no : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | no $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.one]
def unexpTerm_one : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | one $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.lone]
def unexpTerm_lone : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | lone $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.some]
def unexpTerm_some : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | some $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.not]
def unexpTerm_not : Unexpander
  | `($_ [alloy'|$body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | not $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.or]
def unexpTerm_or : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body or $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.and]
def unexpTerm_and : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body and $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.implication]
def unexpTerm_implication : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body => $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.equivalent]
def unexpTerm_equivalent : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body <=> $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

/- expr if else-/
@[app_unexpander ThoR.Semantics.FormulaTerm.f_if_then_else]
def unexpTerm_f_if_then_else : Unexpander
  | `($_ [alloy'|$condition] [alloy'|$thenBody] [alloy'|$elseBody] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |
        $condition:delaborator_body =>
        $thenBody:delaborator_body else
        $elseBody:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.algebraic_leq]
def unexpTerm_algebraic_leq : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body <= $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.algebraic_geq]
def unexpTerm_algebraic_geq : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body >= $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.algebraic_eq]
def unexpTerm_algebraic_eq : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body = $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.algebraic_lt]
def unexpTerm_algebraic_lt : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body < $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.algebraic_gt]
def unexpTerm_algebraic_gt : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body > $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.in]
def unexpTerm_in : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body in $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.eq]
def unexpTerm_eq : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body = $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.neq]
def unexpTerm_neq : Unexpander
  | `($_ [alloy'|$param1] [alloy'|$param2] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body | $param1:delaborator_body != $param2:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit
