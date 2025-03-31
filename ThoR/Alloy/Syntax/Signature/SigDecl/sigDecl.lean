/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Shared.Syntax.mult

import ThoR.Alloy.Syntax.Signature.FieldDecl.fieldDecl
import ThoR.Alloy.Syntax.Signature.Inheritance

import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent

open Shared Lean

namespace Alloy

  /--
  This structure represents a Alloy signature declaration.
  -/
  structure sigDecl where
    mk :: (abs : Bool) -- abstract
          (mult: Shared.mult)
          (names : List (String)) -- min 1
          (extension : sigExt)
          (fieldDecls : List (fieldDecl))
  deriving Repr

  /--
  This Syntax represents a Alloy signature declaration.
  -/
  declare_syntax_cat sigDecl
  abbrev SigDecl := TSyntax `sigDecl
  syntax
    (mult)?
    "sig" extendedIdent,+
    (sigExtExtends <|> sigExtIn)? "{"
    fieldDecl,*
  "}" : sigDecl
  syntax
    ("abstract")?
    "sig" extendedIdent,+
    (sigExtExtends <|> sigExtIn)? "{"
    fieldDecl,*
  "}" : sigDecl
  syntax
    "abstract"
    mult
    "sig" extendedIdent,+
    (sigExtExtends <|> sigExtIn)? "{"
    fieldDecl,*
  "}" : sigDecl

  namespace sigDecl

    instance : Inhabited sigDecl where
      default := {
            abs := false,
            mult := mult.lone,
            names := [],
            extension := sigExt.none,
            fieldDecls := []
          }

    instance : ToString sigDecl where
      toString (sd : sigDecl) : String :=
        s!"sigDecl :\{
            abstract := {sd.abs}
            names := {sd.names},
            multiplicity := {sd.mult},
            extension := {sd.extension},
            fields := {sd.fieldDecls}
          }"

    /--
    Generates a String representation from the structure
    -/
    def toString (sd : sigDecl) : String := ToString.toString sd

    /--
    Adds a single field declaration to the signature
    -/
    def addFieldDecl (sd : sigDecl) (fd : fieldDecl) : sigDecl :=
      {sd with fieldDecls := sd.fieldDecls.append [fd]}

  end sigDecl

end Alloy
