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
  deriving Repr, BEq, Inhabited

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
            let components :=
              eie.foldl (fun result elem =>
                match elem with
                  | `(separatedNamespaceExtension| / $nei:extendedIdent) =>
                    result.concat (extendedIdent.toName nei)
                  | _ => result
              ) [(extendedIdent.toName ei)]

            return {representedNamespace := (mkIdent (Name.fromComponents components))}

          | _ => default

    def toTerm
      (sn : separatedNamespace)
      : TSyntax `term := Unhygienic.run do
        return ← `(term| $(sn.representedNamespace))

    def toSyntax
      (sn : separatedNamespace)
      : TSyntax `separatedNamespace := Unhygienic.run do
        let comps := sn.representedNamespace.getId.components
        let fc := comps.get! 0

        let mut extensions : TSyntaxArray `separatedNamespaceExtension := #[]

        for extension in comps.drop 1 do
          let snExtension ← `(separatedNamespaceExtension| / $(extendedIdent.mkEIdent extension))
          extensions := extensions.push snExtension

        let result ←
          `(separatedNamespace|
            $(extendedIdent.mkEIdent fc):extendedIdent
            $(extensions):separatedNamespaceExtension*
          )

        return result

  end separatedNamespace

end Alloy
