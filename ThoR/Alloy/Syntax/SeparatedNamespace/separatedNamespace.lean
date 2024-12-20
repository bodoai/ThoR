/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
import ThoR.Alloy.Syntax.SeparatedNamespace.extendedIdent
open Lean

/-
  Represents an alloy-like namespace
-/
namespace Alloy

  /--
  This Structure represents the ident value of the alloy-like namespace
  -/
  structure separatedNamespace where
    (representedNamespace : Ident)
  deriving Repr

  /--
  A syntax repreaentation of an separatedNamespace
  -/
  declare_syntax_cat separatedNamespace
  declare_syntax_cat separatedNamespaceExtension
  syntax "/" extendedIdent : separatedNamespaceExtension
  syntax extendedIdent (separatedNamespaceExtension)*: separatedNamespace

  instance : ToString separatedNamespace where
    toString (sn : separatedNamespace) : String :=
      s!"separatedNamespace : {sn.representedNamespace.getId}"

  instance : Inhabited separatedNamespace where
    default := {representedNamespace := default}

  namespace separatedNamespace

    /-- Generates a String representation from the type -/
    def toString (sn : separatedNamespace) : String := ToString.toString sn

    /-- Generates a type representation from the TSyntax -/
    def toType
      (sn : TSyntax `separatedNamespace)
      : separatedNamespace := Id.run do
        match sn with
          | `(separatedNamespace| $ei:extendedIdent) =>

            return {representedNamespace := mkIdent (extendedIdent.toName ei)}

          | `(separatedNamespace|
                $ei:extendedIdent $eie:separatedNamespaceExtension*) =>
            let finalName :=
              eie.foldl (fun result elem =>
                match elem with
                  | `(separatedNamespaceExtension| / $ei:extendedIdent) =>
                    result.appendAfter s!".{extendedIdent.toName ei}"
                  | _ => result
              ) (extendedIdent.toName ei)

            return {representedNamespace := (mkIdent finalName)}

          | _ => default

    def toTerm
      (sn : separatedNamespace)
      : TSyntax `term := Unhygienic.run do
        return ← `(term| $(sn.representedNamespace))

  end separatedNamespace

end Alloy
