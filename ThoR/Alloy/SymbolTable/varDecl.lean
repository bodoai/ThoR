/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax

open Shared

namespace Alloy

  /--
  This structure represents a (Lean) variable declaration.
  -/
  structure varDecl where
    mk :: (name : String)
          (type : typeExpr)
          (requiredDecls : List (String))
  deriving Repr

  namespace varDecl

    /-- Generates a String representation from the type -/
    def toString (vd : varDecl) : String :=
      s!"variableDeclaration : \{
        name := {vd.name},
        type := {vd.type},
        requiredDeclarations := {vd.requiredDecls}
      }"

    instance : ToString varDecl where
      toString := toString

    instance : BEq varDecl where
      beq : varDecl -> varDecl -> Bool
        | vd1, vd2 => (vd1.name == vd2.name) && (vd1.type == vd2.type)

    instance : Inhabited varDecl where
      default := {  name:= "default",
                    type := typeExpr.multExpr mult.set
                      (expr.string "default"),
                    requiredDecls := []
                  }

  end varDecl

end Alloy
