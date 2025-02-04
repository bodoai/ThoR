/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.TypeExpr.typeExpr

import ThoR.Alloy.Config

open Shared Config

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

    def getFullRelationName (vd : varDecl) : String :=
      s!"{if vd.isOpened then s!"{vd.openedFrom.replace "_" "."}." else ""}\
      {vd.relationOf}.\
      {vd.name}"

    def getRelationReplacementName (vd : varDecl) : String :=
      s!"{vd.openedFrom}\
      {signatureSeparator}\
      {vd.relationOf}\
      {relationSeparator}\
      {vd.name}"

    def getFullSignatureName (vd : varDecl) : String :=
      s!"{if vd.isOpened then s!"{vd.openedFrom.replace "_" "."}." else ""}\
      {vd.name}"

    def getSignatureReplacementName (vd : varDecl) : String :=
      s!"{vd.openedFrom}\
      {signatureSeparator}\
      {vd.name}"

  end varDecl

end Alloy
