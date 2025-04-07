/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
The purpose of this file is to encapsulate the extension types and contains
service functions to manage them.
-/
import ThoR.Basic

import ThoR.Shared.Syntax.TypeExpr.typeExpr

import ThoR.Alloy.Syntax.Signature.Inheritance.sigExtExtends
import ThoR.Alloy.Syntax.Signature.Inheritance.sigExtIn

open Shared
open Lean

namespace Alloy

  /--
  This inductive type represents an (or no) extension
  of an Alloy signature declaration
  -/
  inductive sigExt
    | none
    | extends : (extension : sigExtExtends) → sigExt
    | in : (extension : sigExtIn) → sigExt
  deriving Repr

  instance : BEq sigExt where
    beq :  sigExt -> sigExt -> Bool
      | sigExt.none, sigExt.none => true
      | sigExt.extends _, sigExt.extends _ => true
      | sigExt.in _, sigExt.in _ => true
      | _, _ => false

  instance : ToString sigExt where
    toString (se : sigExt) : String :=
      match se with
        | sigExt.none => "none"
        | sigExt.extends e => e.toString
        | sigExt.in i => i.toString
  namespace sigExt

    /--
    Generates a string represeantation of the type
    -/
    def toString (se : sigExt) := ToString.toString se

    /--
    Creates an 'in' extension
    -/
    def createSigExtIn
      (name : Ident)
      (type : TSyntaxArray `sigExtInType)
      := sigExt.in (sigExtIn.create name type)

    /--
    Creates an 'in' extension if the given Options are not empty
    (else creates a 'none' extension)
    -/
    def fromOptionIn
      (extensionName : Option (Ident))
      (typeExtensions : Option (TSyntaxArray `sigExtInType))
      : sigExt :=
        match extensionName with
          | Option.some en => (createSigExtIn en typeExtensions.get!)
          | Option.none => sigExt.none

    /--
    Creates an 'extends' extension
    -/
    def createSigExtExtends
      (name : Ident)
      := sigExt.extends (sigExtExtends.create name)

    /--
    Creates an 'extends' extension if the given Options are not empty
    (else creates a 'none' extension)
    -/
    def fromOptionEx
      (extensionName : Option (Ident))
      : sigExt :=
        match extensionName with
          | Option.some en => (createSigExtExtends en)
          | Option.none => sigExt.none

    /--
    Gets the type of the extension
    -/
    def getType (se : sigExt) (m : mult := mult.set)
      : typeExpr :=
      match se with
        | sigExt.extends ext => (ext.type)
        | sigExt.in extIn => (extIn.type)
        | sigExt.none => -- no extension is univ
            typeExpr.multExpr m
                (expr.const constant.univ)

  end sigExt

end Alloy
