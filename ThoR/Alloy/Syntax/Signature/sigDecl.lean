/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Shared.Syntax.mult

import ThoR.Alloy.Syntax.Signature.fieldDecl
import ThoR.Alloy.Syntax.Signature.Inheritance

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
  syntax
    (mult)?
    "sig" ident,+
    (sigExtExtends <|> sigExtIn)? "{"
    fieldDecl,*
  "}" : sigDecl
  syntax
    ("abstract")?
    "sig" ident,+
    (sigExtExtends <|> sigExtIn)? "{"
    fieldDecl,*
  "}" : sigDecl
  syntax
    "abstract"
    mult
    "sig" ident,+
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

    /--
    Creates a signature declaration from the parameters
    -/
    def create
      (names : Syntax.TSepArray `ident ",")
      (mult : Shared.mult)
      (abstr : Bool)
      (extension : sigExt)
      (fields : Syntax.TSepArray `fieldDecl ",")
      : sigDecl := Id.run do
        --Identifier to String
        let stringNames : List (String) :=
          (names.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList

        let mut newSigDecl : sigDecl := {
            abs := abstr,
            mult := mult,
            names := stringNames,
            extension := extension,
            fieldDecls := [],
          }

        for field in fields.getElems do
          match field with
          -- only one case
          | `(fieldDecl | $relNames:ident,* : $te:typeExpr) => do
            let stringNames : List (String) :=
              (relNames.getElems.map fun (elem) => elem.getId.lastComponentAsString).toList

            let type := typeExpr.toType te

            newSigDecl := addFieldDecl newSigDecl
                    ({names:= stringNames,
                      type:= type
                      }:fieldDecl)

          | _ => unreachable!

        return newSigDecl

    /--
    Parses the given syntax to a sigDecl (type) if possible
    -/
    def toType (sd: TSyntax `sigDecl) : sigDecl :=
      match sd with
        -- signature with opt mult, extends, fields
        | `(sigDecl|
            $m:mult sig $sigNames:ident,*
            $[extends $extensionName]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.toType m)
          false (sigExt.fromOptionEx extensionName) fields

        -- abstract signature, extends, fields
        | `(sigDecl|
            abstract
            sig $sigNames:ident,*
            $[extends $extensionName]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.set)
          true (sigExt.fromOptionEx extensionName) fields

        -- abstract signature with mult, extends, fields
        | `(sigDecl|
            abstract $m:mult sig $sigNames:ident,*
            $[extends $extensionName]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.toType m)
          false (sigExt.fromOptionEx extensionName) fields

        -- simple sig with extends
        | `(sigDecl|
            sig $sigNames:ident,*
            $[extends $extensionName]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.set)
          false (sigExt.fromOptionEx extensionName) fields

        -- signature with opt mult, in, fields
        | `(sigDecl|
            $m:mult sig $sigNames:ident,*
            $[in $extensionName $typeExtensions*]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.toType m)
          false (sigExt.fromOptionIn extensionName typeExtensions) fields

        -- abstract signature with in, fields
        | `(sigDecl|
            abstract
            sig $sigNames:ident,*
            $[in $extensionName $typeExtensions*]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.set)
          true (sigExt.fromOptionIn extensionName typeExtensions) fields

        -- abstract signature with mult in, fields
        | `(sigDecl|
            abstract $m:mult sig $sigNames:ident,*
            $[in $extensionName $typeExtensions*]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.toType m)
          true (sigExt.fromOptionIn extensionName typeExtensions) fields

        -- simple sig with in
        | `(sigDecl|
            sig $sigNames:ident,*
            $[in $extensionName $typeExtensions*]?
              { $fields:fieldDecl,* }
          ) =>
         create sigNames (mult.set)
          true (sigExt.fromOptionIn extensionName typeExtensions) fields


        | _ => {
            abs := false,
            mult := mult.lone,
            names := ["PANIC! PARSING ERROR"],
            extension := sigExt.none,
            fieldDecls := []
          }

  end sigDecl

end Alloy
