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
          (isOpened : Bool) -- imported
          (openedFrom : String)
          (isRelation : Bool)
          (relationOf : String)
          (type : typeExpr)
          (requiredDecls : List (String))
  deriving Repr

  namespace varDecl

    /-- Generates a String representation from the type -/
    def toString (vd : varDecl) : String :=
      s!"variableDeclaration : \{
        name := {vd.name},
        isOpenend := {vd.isOpened},
        openedFrom := {vd.openedFrom},
        isRelationOf := {vd.isRelation},
        relationOf := {vd.relationOf},
        type := {vd.type},
        requiredDeclarations := {vd.requiredDecls}
      }"

    instance : ToString varDecl where
      toString := toString

    instance : BEq varDecl where
      beq : varDecl -> varDecl -> Bool
        | vd1, vd2 => (vd1.name == vd2.name) &&
                        (vd1.type == vd2.type) &&
                          (vd1.isRelation == vd2.isRelation) &&
                            (vd1.requiredDecls == vd2.requiredDecls)

    instance : Inhabited varDecl where
      default := {  name:= default,
                    isOpened := default,
                    openedFrom := default,
                    isRelation := default,
                    relationOf := default,
                    type := default,
                    requiredDecls := default
                  }

  end varDecl

end Alloy
