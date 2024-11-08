/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Shared.Syntax.typeExpr
open Shared Lean

namespace Alloy

  /--
  This strucutre represents an 'in' extension of a Alloy signature declaration
  -/
  structure sigExtIn where
    mk :: (type : typeExpr) -- min 1
  deriving Repr

  /--
  This syntax represents an 'in' extension of a Alloy signature declaration
  -/
  declare_syntax_cat sigExtIn
  declare_syntax_cat sigExtInType
  syntax "+" ident : sigExtInType
  syntax (" in " ident sigExtInType*) : sigExtIn

  instance : ToString sigExtIn where
    toString (sei : sigExtIn) : String := Id.run do
      s!"in {sei.type.toString}"

  /--
  Joins the ginven expressions with +
  -/
  private def createUnion (e : expr) (es : List (expr)) : expr :=
    match es with
      | (head :: tail) => expr.binaryRelOperation (binRelOp.union) e (createUnion head tail)
      | [] => e

  namespace sigExtIn

    /--
    Generates a string representation of the structure
    -/
    def toString (sei : sigExtIn) : String := ToString.toString sei

    /--
    Creates the extension strucutre from the given name and syntax.
    -/
    def create
      (name : TSyntax `ident)
      (typeExtensions : TSyntaxArray `sigExtInType)
      : sigExtIn := Id.run do

        let name := name.getId.lastComponentAsString

        let mut type : typeExpr := (typeExpr.multExpr mult.set (expr.string name))
        if !(typeExtensions.isEmpty) then

          let mut tes : List (expr) := []
          for te in typeExtensions do
            match te with
              | `(sigExtInType| + $extender) =>
                tes := tes.append [(expr.string extender.getId.lastComponentAsString)]
              | _ => unreachable!

          type := (typeExpr.multExpr mult.set (createUnion (expr.string name) (tes)))

        return {type := type}


  end sigExtIn

end Alloy
