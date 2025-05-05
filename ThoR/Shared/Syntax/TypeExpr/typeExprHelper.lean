/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the data structures-/
import ThoR.Shared.Syntax.Mutuals.mutuals

/- import the exprHelper functions -/
import ThoR.Shared.Syntax.Relation.Expr.exprHelper

namespace Shared.typeExpr
  def isString
    | typeExpr.relExpr e => e.isString
    | typeExpr.multExpr _ e => e.isString
    | _ => false

  def getStringData
    | typeExpr.relExpr e => e.getStringData
    | typeExpr.multExpr _ e => e.getStringData
    | e => panic! s!"Tried to get String data from expr {e}"

  def getStringExpr (te:typeExpr) : String :=
    match te with
      | typeExpr.multExpr _ e => e.getStringExpr
      | typeExpr.relExpr e => e.getStringExpr
      | typeExpr.arrowExpr _ => default

end Shared.typeExpr
