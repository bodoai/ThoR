/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.Signature.SigDecl.sigDecl
import ThoR.Alloy.Syntax.Signature.FieldDecl.fieldDeclService

open Lean Shared

namespace Alloy.sigDecl

  def insertModuleVariables
    (sd : sigDecl)
    (moduleVariables openVariables : List (String))
    : sigDecl :=
    let fieldDecls := sd.fieldDecls.map
      fun fd => fd.insertModuleVariables moduleVariables openVariables
    {sd with fieldDecls := fieldDecls}

  /--
  Creates a signature declaration from the parameters
  -/
  def create
    (names : Syntax.TSepArray `extendedIdent ",")
    (mult : Shared.mult)
    (abstr : Bool)
    (extension : sigExt)
    (fields : Syntax.TSepArray `fieldDecl ",")
    : sigDecl := Id.run do
      --Extended Identifier to String
      let stringNames : List (String) :=
        ( names.getElems.map fun (elem) =>
          (extendedIdent.toName elem).toString
        ).toList

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
        | `(fieldDecl | $relNames:extendedIdent,* : $te:typeExpr) => do
          let stringNames : List (String) :=
            ( relNames.getElems.map fun (elem) =>
              (extendedIdent.toName elem).toString
            ).toList

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
  def toType (sd: SigDecl) : sigDecl :=
    match sd with
      -- signature with opt mult, extends, fields
      | `(sigDecl|
          $m:mult sig $sigNames:extendedIdent,*
          $[extends $extensionName]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.toType m)
        false (sigExt.fromOptionEx extensionName) fields

      -- abstract signature, extends, fields
      | `(sigDecl|
          abstract
          sig $sigNames:extendedIdent,*
          $[extends $extensionName]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.set)
        true (sigExt.fromOptionEx extensionName) fields

      -- abstract signature with mult, extends, fields
      | `(sigDecl|
          abstract $m:mult sig $sigNames:extendedIdent,*
          $[extends $extensionName]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.toType m)
        false (sigExt.fromOptionEx extensionName) fields

      -- simple sig with extends
      | `(sigDecl|
          sig $sigNames:extendedIdent,*
          $[extends $extensionName]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.set)
        false (sigExt.fromOptionEx extensionName) fields

      -- signature with opt mult, in, fields
      | `(sigDecl|
          $m:mult sig $sigNames:extendedIdent,*
          $[in $extensionName $typeExtensions*]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.toType m)
        false (sigExt.fromOptionIn extensionName typeExtensions) fields

      -- abstract signature with in, fields
      | `(sigDecl|
          abstract
          sig $sigNames:extendedIdent,*
          $[in $extensionName $typeExtensions*]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.set)
        true (sigExt.fromOptionIn extensionName typeExtensions) fields

      -- abstract signature with mult in, fields
      | `(sigDecl|
          abstract $m:mult sig $sigNames:extendedIdent,*
          $[in $extensionName $typeExtensions*]?
            { $fields:fieldDecl,* }
        ) =>
        create sigNames (mult.toType m)
        true (sigExt.fromOptionIn extensionName typeExtensions) fields

      -- simple sig with in
      | `(sigDecl|
          sig $sigNames:extendedIdent,*
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

  def toTerm (sd : sigDecl) : Term := Unhygienic.run do
    let absTerm ← `(term | $(if sd.abs then (mkIdent `true) else (mkIdent `false)))
    let multTerm := sd.mult.toTerm

    let mut namesTerm : Term ← `(term | (List.nil))
    for name in sd.names.reverse do
      namesTerm  ← `(term | (List.cons $(Lean.Syntax.mkStrLit name) ($namesTerm)))

    return ← `(term | ({
                          abs := $absTerm,
                          mult := $multTerm,
                          names := $namesTerm,
                          extension := Alloy.sigExt.none,
                          fieldDecls := []
                      } : Alloy.sigDecl ))

end Alloy.sigDecl
