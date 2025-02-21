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

    /-- Generates a String representation from the type -/
    def toString (vd : varDecl) : String :=
      s!"variableDeclaration : \{
        name := {vd.name},
        isOpenend := {vd.isOpened},
        openedFrom := {vd.openedFrom},
        isRelationOf := {vd.isRelation},
        relationOf := {vd.relationOf},
        isQuantor := {vd.isQuantor}
        type := {vd.type},
        requiredDeclarations := {vd.requiredDecls}
      }"

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
