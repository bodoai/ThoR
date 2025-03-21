/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.TypeExpr.typeExpr

import ThoR.Alloy.Config

open Shared Config Lean

namespace Alloy

  /--
  This structure represents a (Lean) variable declaration.
  -/
  structure varDecl where
    mk :: (name : String)
          (isOpened : Bool) -- imported from another module
          /-
          the FULL name of the other module
          e.g. m1/te is m1_te
          -/
          (openedFrom : String)
          (isRelation : Bool)
          (relationOf : String)
          (isQuantor : Bool) -- if it is a temp quantor declaration
          (type : typeExpr)
          (requiredDecls : List (String))
  deriving Repr, BEq

  namespace varDecl

    def updateType (vd : varDecl) (type : typeExpr) : varDecl :=
      {vd with type := type}

    def toString
      (vd : varDecl)
      (inner_space_count := 3)
      (outer_space_count := 1)
      (leading_new_line := false)
      : String := Id.run do

      let mut inner_spaces : String := ""
      for _ in [0:inner_space_count] do
        inner_spaces := inner_spaces ++ " "

      let mut outer_spaces : String := ""
      for _ in [0:outer_space_count] do
        outer_spaces := outer_spaces ++ " "

      let result :=
        outer_spaces ++ "variable declaration : ⦃ \n" ++
        inner_spaces ++ s!"name := {vd.name}" ++ "\n" ++
        inner_spaces ++ s!"is openend := {vd.isOpened}," ++ "\n" ++
        inner_spaces ++ s!"opened from := {vd.openedFrom}," ++ "\n" ++
        inner_spaces ++ s!"is relation of := {vd.isRelation}," ++ "\n" ++
        inner_spaces ++ s!"relation of := {vd.relationOf}," ++ "\n" ++
        inner_spaces ++ s!"is quantor := {vd.isQuantor}," ++ "\n" ++
        inner_spaces ++ s!"type := {vd.type}," ++ "\n" ++
        inner_spaces ++ s!"required declarations := {vd.requiredDecls}" ++ "\n" ++
        outer_spaces ++ "⦄"

      if leading_new_line then
        "\n" ++ result
      else
        result

    instance : ToString varDecl where
      toString := toString

    instance : Inhabited varDecl where
      default := {  name:= default,
                    isOpened := default,
                    openedFrom := default,
                    isRelation := default,
                    relationOf := default,
                    isQuantor := default,
                    type := default,
                    requiredDecls := default
                  }

    def getFullRelationName (vd : varDecl) : Name := Id.run do
      Name.fromComponents
        (
          ( if vd.isOpened then
              ((vd.openedFrom.splitOn "_").map
                fun elem => elem.toName)
            else
              []
          )
          ++ [vd.relationOf.toName, vd.name.toName])

    def getRelationReplacementName (vd : varDecl) : String :=
      s!"{vd.openedFrom}\
      {signatureSeparator}\
      {vd.relationOf}\
      {relationSeparator}\
      {vd.name}"

    def getFullSignatureName (vd : varDecl) : Name :=
      Name.fromComponents
        (
          ( if vd.isOpened then
              ((vd.openedFrom.splitOn "_").map
                fun elem => elem.toName)
            else
              []
          )
          ++ [vd.name.toName])

    def getSignatureReplacementName (vd : varDecl) : String :=
      s!"{vd.openedFrom}\
      {signatureSeparator}\
      {vd.name}"

  end varDecl

end Alloy
