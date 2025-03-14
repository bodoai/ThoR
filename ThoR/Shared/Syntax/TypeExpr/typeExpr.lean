/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.mult
import ThoR.Shared.Syntax.ArrowOp.arrowOp

open ThoR
open Lean

namespace Shared

  /--
  This inductive type represents a typeExpression
  -/
  inductive typeExpr
    | arrowExpr : (arrowExpr : arrowOp) → typeExpr
    | multExpr :
        (m : mult) →
        (expr : expr) →
        typeExpr
    | relExpr :
        (expr : expr) →
        typeExpr
  deriving Repr

  /--
  This syntax represents a typeExpression
  -/
  declare_syntax_cat typeExpr
  abbrev TypeExpr := TSyntax `typeExpr
  syntax arrowOp : typeExpr
  syntax expr : typeExpr
  syntax mult expr : typeExpr

  instance : ToString typeExpr where
    toString : typeExpr -> String
      | typeExpr.arrowExpr ae => ae.toString
      | typeExpr.multExpr m e => (m.toString) ++ " " ++ (e.toString)
      | typeExpr.relExpr e => e.toString

  instance : BEq typeExpr where
    beq : typeExpr -> typeExpr -> Bool
      | typeExpr.arrowExpr ae1, typeExpr.arrowExpr ae2 => ae1 == ae2
      | typeExpr.multExpr m1 e1, typeExpr.multExpr m2 e2 => (m1 == m2) && (e1 == e2)
      | typeExpr.relExpr e1, typeExpr.relExpr e2 => e1 == e2
      | _, _ => false
  namespace typeExpr

  instance : Inhabited typeExpr where
    default := typeExpr.relExpr default

    /--
    Generates a string representation of the type
    -/
    def toString (te : typeExpr) : String := s!"{te}"

  end typeExpr

end Shared
