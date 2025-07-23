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

open Shared Alloy


@[app_unexpander ThoR.Semantics.ExpressionTerm.local_rel_var]
def unexpTerm_local_rel_var : Unexpander
  | `($_ $_:ident $name:str) => do

    let name_ident := mkIdent name.getString.toName

    let bb := unhygienicUnfolder
      `(delaborator_body | $name_ident:ident )

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

@[app_unexpander ThoR.Semantics.Term.formula]
def unexpTerm_formula : Unexpander
  | `($_ [alloy'| $body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |  $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.expr]
def unexpTerm_expression : Unexpander
  | `($_ [alloy'| $body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |  $body:delaborator_body )

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.Term.bracket]
def unexpTerm_bracket : Unexpander
  | `($_ [alloy'| $body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |  ($body:delaborator_body ))

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.ExpressionTerm.bracket]
def unexpExpressionTerm_bracket : Unexpander
  | `($_ [alloy'| $body] ) => do
    let bb := unhygienicUnfolder
      `(delaborator_body |  ($body:delaborator_body ))

    `([alloy' | $bb:delaborator_body ])

  | _ => throw Unit.unit

@[app_unexpander ThoR.Semantics.FormulaTerm.bracket]
def unexpFormulaTerm_bracket : Unexpander
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


private partial def getType
  (type : TSyntax `term)
  : TSyntax `delaborator_body × Bool := Id.run do
    let mut showType := true

    let mut final_type := unhygienicUnfolder `(delaborator_body| $(mkIdent `t):ident)

    match type with
      | `([alloy'| $body].eval) => final_type := body
      | `([alloy'| $body]) => final_type := body
      | _ => showType := false

    return (final_type, showType)

private structure delabArg where
  (name : (TSyntax `delaborator_body))
  (type : (TSyntax `delaborator_body))
  (showType : Bool)

instance : Inhabited delabArg where
  default := {name := default, type := default, showType := false}

private partial def getArgs
  (body : TSyntax `term)
  : (Array delabArg) × (TSyntax `delaborator_body)
  := Id.run do
  let mut result := #[]
  let mut trueBody := unhygienicUnfolder `(delaborator_body|$(mkIdent `default):ident)
  match body with
    /- Either lam -/
    | `(ThoR.Semantics.Term.lam $type $lambda_function) =>

      let type_and_showType := getType type
      let type := type_and_showType.1
      let showType := type_and_showType.2

      match lambda_function with
        | `(fun $lambda_variable ↦ $body) =>
          match lambda_variable with
            | `( Lean.Parser.Term.funBinder |
                $(variable_nameTerm):term ) =>
                  match variable_nameTerm with
                    | `($variable_name:ident) =>
                      let arg :=
                        unhygienicUnfolder
                          `(delaborator_body |
                            $variable_name:ident)

                      result :=
                        result.push
                          { name := arg,
                            type :=type,
                            showType := showType }

                    | _ => result := result

          /- if the body (inside lam) is not a lam then its the final body -/
          match body with
            | `([alloy'| $body]) =>
              trueBody := body
            | _ =>
              let subResult := (getArgs body)
              result := result.append subResult.1.reverse
              trueBody := subResult.2

        | _ => result := result

    /- or can be a direct body -/
    | `([alloy'| $body]) =>
      trueBody := body

    | _ => result := result

  (result.reverse, trueBody)

open Std in
private def groupArgs
  (args : Array delabArg)
  : Array (TSyntax `delabArg)
  := Id.run do
  let mut args_per_type
    : (HashMap String (List delabArg))
    := HashMap.emptyWithCapacity

  for arg in args do
    let type_as_string := s!"{arg.type.raw}"
    args_per_type :=
      args_per_type.insert type_as_string
        ((args_per_type.getD type_as_string []).concat arg)

  let mut groupedArgs := #[]
  for type_with_args in args_per_type.toList do
    let args := type_with_args.2
    if !args.isEmpty then
      let argNames := (type_with_args.2.map fun a => a.name).toArray

      let firstArg := (type_with_args.2[0]!)
      let type := firstArg.type
      let showType := firstArg.showType

      if showType then
        groupedArgs :=
          groupedArgs.push
            (unhygienicUnfolder
              `(delabArg | $[$(argNames)],* : $type ))
      else
        for name in argNames do
          groupedArgs :=
            groupedArgs.push
              (unhygienicUnfolder
                `(delabArg | $name:delaborator_body ))

  return groupedArgs

@[app_unexpander ThoR.Semantics.Term.pred_def]
def unexpTerm_predDef : Unexpander
  | `($_ $name $body ) => do

    let nn := match name with
      | `(term | $n:str) => n.getString
      | _ => "Error matching Name"

    /-get args here to group them-/
    let argsAndBody := getArgs body
    let args := argsAndBody.1
    let groupedArgs := groupArgs args

    let argsBody := unhygienicUnfolder `(delaborator_body | [$[$(groupedArgs)],*])
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
      | _ => "Error matching Name"

    /-get args here to group them-/
    let argsAndBody := getArgs body
    let args := argsAndBody.1
    let groupedArgs := groupArgs args

    let argsBody := unhygienicUnfolder `(delaborator_body | [$[$(groupedArgs)],*])
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

private def quantExtractor (t :Term) : Except String Shared.quant := do
  match t with
    | `(Shared.quant.all) => return quant.all
    | `(Shared.quant.some) => return quant.some
    | `(Shared.quant.lone) => return quant.lone
    | `(Shared.quant.one) => return quant.one
    | `(Shared.quant.no) => return quant.no
    | _ => throw s!"Could not find match "

private def quant.toDelabQuantor (q : Shared.quant) : DelabQuantor :=
  match q with
    | .all => unhygienicUnfolder `(delabQuantor | all)
    | .some =>unhygienicUnfolder `(delabQuantor | some)
    | .lone => unhygienicUnfolder `(delabQuantor | lone)
    | .one => unhygienicUnfolder `(delabQuantor | one)
    | .no => unhygienicUnfolder `(delabQuantor | no)

private def boolExtractor (t : Term) : Except String Bool := do
  match t with
    | `(false) => return false
    | `(true) => return true
    | _ => throw s!"Could not find match "

private structure bind_collection where
  (quantor : DelabQuantor)
  (showDisj : Bool)

private def getBindCollection
  (quantor disjoint : Term)
  : Except String bind_collection := do
    let quantor ← (quantExtractor quantor)
    let delab_quantor := quant.toDelabQuantor quantor
    let showDisj ←  boolExtractor disjoint
    return  {
              quantor := delab_quantor,
              showDisj := showDisj
            }

/- quantor bind -/
@[app_unexpander ThoR.Semantics.FormulaTerm.bind]
def unexpFormulaTerm_bind : Unexpander
  | `($_ $quantor_type $disjoint $names $type:str $body) => do
    let bindCollection := getBindCollection quantor_type disjoint
    match bindCollection with
      | Except.error _ => throw Unit.unit
      | Except.ok bindCollection =>

        let names : TSyntax `delabArg := match names with
          | `(#[ $[$str_names:str],* ].toVector) =>
              let argBodies :=
                str_names.map fun n =>
                  unhygienicUnfolder `(delaborator_body | $(mkIdent n.getString.toName))

              unhygienicUnfolder
                `(delabArg |
                  $[$(argBodies)],* : $(mkIdent type.getString.toName))

          | _ => default

        let body := unhygienicUnfolder `(delaborator_body | { $(mkIdent `TODO) } )

        let bb :=
          if bindCollection.showDisj then
            unhygienicUnfolder
            `(delaborator_body |
              $bindCollection.quantor:delabQuantor
              disj
              $(names)
              |
              $(body)
            )
          else
            unhygienicUnfolder
            `(delaborator_body |
              $bindCollection.quantor:delabQuantor
              $(names)
              |
              $(body)
            )

        `([alloy' | $bb:delaborator_body ])


  | _ => throw Unit.unit
