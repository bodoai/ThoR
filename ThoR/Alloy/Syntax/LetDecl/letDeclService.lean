/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.LetDecl.letDecl
import ThoR.Shared.Syntax.Formula.formulaService
import ThoR.Shared.unhygienicUnfolder

open Shared Lean

namespace Alloy.letDecl

  def toType (ld : LetDecl) : letDecl :=
    match ld with
      | `(letDecl | let $name:ident = $value:formula | $body:formula) =>
        { name := name.getId,
          value := formula.toType value,
          body := [formula.toType body] }
      | `(letDecl | let $name:ident = $value:formula | {$body:formula*}) =>
        { name := name.getId,
          value := formula.toType value,
          body := (body.map fun e => formula.toType e).toList }
      | _ => default

  def toTerm
  (ld : letDecl)
  (blockName : Name)
  (variableNames : List (String)) -- to check if var or pred
  (callableVariables : List (varDecl))
  (callablePredicates : List (commandDecl × List (expr × List (String × List varDecl))))
  : Except String (List Term) := do
    let name := mkIdent ld.name
    let value ← ld.value.toTerm blockName variableNames callableVariables callablePredicates
    let ebody :=
      (ld.body.map fun e =>
        e.toTerm blockName variableNames callableVariables callablePredicates
        )
    let mut body : List Term := []
    for elem in ebody do
      match elem with
        | Except.error msg => throw msg
        | Except.ok data => body := body.concat data

    let letTerm : Term :=
    unhygienicUnfolder `(let $(name):ident := $(value):term; $(value):term)

    return [letTerm].append body

end Alloy.letDecl
