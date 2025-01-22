/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Relation.Quantification
import ThoR.Relation.Rel

import ThoR.Shared.Syntax.Formula.formula

open ThoR
open ThoR.Quantification
open ThoR.Quantification.Formula

open Lean PrettyPrinter Delaborator SubExpr Expr

def extractVarName (e:Expr) : Name :=
  match e with
  | Expr.app name arg => extractVarName arg
  | Expr.lam binderName binderType body binderInfo => binderName
  | _ => default

def extractType (e:Expr) : Expr :=
  match e with
  | Expr.app name arg => extractType arg
  | Expr.lam binderName binderType body binderInfo => binderType
  | _ => e

def extractBody (e:Expr) : Expr :=
  match e with
  | Expr.app name arg => extractBody arg
  | Expr.lam binderName binderType body binderInfo => body
  | _ => e

@[delab app.ThoR.Quantification.Formula.var]
def delab2 : Delab := do
  let e ← getExpr
  let name := extractVarName e
  let type ← (delab (extractType e))
  let body ← (delab (extractBody e))
  `($(mkIdent name) $(type) $body)

-- TODO How can we get rid of the (obsolete?) syntax
--      category delab_formula?
declare_syntax_cat delab_formula
syntax quant ("disj")? ident,+ " : " term " | " term : delab_formula
syntax delab_formula : term

def extractBVarNames (e:Expr) : List (Name) :=
  match e with
  | Expr.app name arg => extractBVarNames arg
  | Expr.lam bn bt body bi => [bn].append (extractBVarNames body)
  | _ => default

def substituteBVarsWithConst (e:Expr) (bnl : List (Name)) : Expr := Id.run do
  match e with
    | Expr.bvar n => Expr.const (bnl.reverse.get! n) []
    | Expr.app fn arg => Expr.app (substituteBVarsWithConst fn bnl) (substituteBVarsWithConst arg bnl)
    | Expr.lam bn bt body bi => Expr.lam bn bt (substituteBVarsWithConst body (bnl)) bi
    | _ => e

def termToQuant (t : TSyntax `term) : Shared.quant :=
  match t with
  | `(Shared.quant.no) => Shared.quant.no
  | `(Shared.quant.lone) => Shared.quant.lone
  | `(Shared.quant.one) => Shared.quant.one
  | `(Shared.quant.some) => Shared.quant.some
  | `(Shared.quant.all) => Shared.quant.all
  | _ => Shared.quant.no

@[delab app.ThoR.Quantification.Formula.var]
def delab3 : Delab := do
  let e ← getExpr
  let args := (← SubExpr.getExpr).getAppArgs
  let name := extractVarName e
  let type ← (delab (extractType e))

  let pure_body := (extractBody e)

  let ea_body := (substituteBVarsWithConst pure_body (extractBVarNames e))
  let body ← (delab ea_body)
  let q : Shared.quant := (termToQuant (← delab (args.get! 2))) -- quant steht an Pos. 2
  `(term | $(q.toSyntax):quant $(mkIdent name) : $(type) | $(body))

@[app_unexpander ThoR.Quantification.Formula.eval]
def unexpThoRQuantificationFormulaEval : Unexpander
  | `($_ $a) => `($a)
  | _ => throw Unit.unit

@[app_unexpander ThoR.Quantification.Formula.prop]
def unexpThoRQuantificationFormulaProp : Unexpander
  | `($_ $a) => `($a)
  | _ => throw Unit.unit

partial def extractGroupBVarNames (e:Expr) : List (Name) :=
  let fName := e.getAppFn.constName.toString
  match fName with
  | "ThoR.Quantification.Formula.disj" =>
    let groupVarExpr := e.getAppArgs.get! 2
    extractGroupBVarNames groupVarExpr
  | "ThoR.Quantification.Formula.group" =>
    let groupVarExpr := e.getAppArgs.get! 2
    extractGroupBVarNames groupVarExpr
  | "ThoR.Quantification.Group.var" =>
    let lambdaExpr := (e.getAppArgs.get! 1)
    match lambdaExpr with
    | Expr.lam bn bt body bi => [bn].append (extractGroupBVarNames body)
    | _ => []
  | _ => []


partial def extractGroupBody (e:Expr) : Expr :=
  let fName := e.getAppFn.constName.toString
  match fName with
  | "ThoR.Quantification.Formula.disj" =>
    let groupVarExpr := e.getAppArgs.get! 2
    extractGroupBody groupVarExpr
  | "ThoR.Quantification.Formula.group" =>
    let groupVarExpr := e.getAppArgs.get! 2
    extractGroupBody groupVarExpr
  | "ThoR.Quantification.Group.var" =>
    let lambdaExpr := (e.getAppArgs.get! 1)
    match lambdaExpr with
    | Expr.lam bn bt body bi => extractGroupBody body
    | _ => default
  | "ThoR.Quantification.Group.formula" =>
    let formulaExpr := (e.getAppArgs.get! 2)
    formulaExpr
  | _ => default

@[delab app.ThoR.Quantification.Formula.group]
def delab4 : Delab := do
  let e ← getExpr
  let pure_body := (extractGroupBody e)
  let ea_body := (substituteBVarsWithConst pure_body (extractBVarNames e))
  let body ← (delab ea_body)

  let type ← (delab (extractType e))

  let args := e.getAppArgs
  let q : Shared.quant := (termToQuant (← delab (args.get! 1))) -- quant steht an Pos. 2

  let bVarNames := extractGroupBVarNames e
  let namesArray : Array (Ident) :=
    bVarNames.toArray.map fun (e) => mkIdent e

  `(term |  $(q.toSyntax):quant $[ $namesArray ],* : $(type) | $(body))

@[delab app.ThoR.Quantification.Formula.disj]
def delab5 : Delab := do
  let e ← getExpr
  let pure_body := (extractGroupBody e)
  let ea_body := (substituteBVarsWithConst pure_body (extractBVarNames e))
  let body ← (delab ea_body)

  let type ← (delab (extractType e))

  let args := e.getAppArgs
  let q : Shared.quant := (termToQuant (← delab (args.get! 1))) -- quant steht an Pos. 2

  let bVarNames := extractGroupBVarNames e
  let namesArray : Array (Ident) :=
    bVarNames.toArray.map fun (e) => mkIdent e

  `(term |  $(q.toSyntax):quant disj $[ $namesArray ],* : $(type) | $(body))
