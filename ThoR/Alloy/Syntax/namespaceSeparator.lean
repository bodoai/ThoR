/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic
open Lean

/-
  Represents an alloy-like namespace
-/
namespace Alloy

  /--
  This Structure represents the ident value of the alloy-like namespace
  -/
  structure namespaceSeparator where
    (representedNamespace : Ident)
  deriving Repr

  /--
  A syntax repreaentation of an assert declaration.
  -/
  declare_syntax_cat namespaceSeparator
  declare_syntax_cat namespaceSeparatorExtension
  syntax "/" str : namespaceSeparatorExtension
  syntax str (namespaceSeparatorExtension)*: namespaceSeparator

  instance : ToString namespaceSeparator where
    toString (ns : namespaceSeparator) : String :=
      s!"namespaceSeparator : {ns.representedNamespace.getId}"

  instance : Inhabited namespaceSeparator where
    default := {representedNamespace := default}

  namespace namespaceSeparator

    /-- Generates a String representation from the type -/
    def toString (ns : namespaceSeparator) : String := ToString.toString ns

    /-- Generates a type representation from the TSyntax -/
    def toType
      (ns : TSyntax `namespaceSeparator)
      : namespaceSeparator := Id.run do
        match ns with
          | `(namespaceSeparator| $ns:str) =>
            return {representedNamespace := (mkIdent ns.getString.toName)}

          | `(namespaceSeparator|
                $ns:str $nse:namespaceSeparatorExtension*) =>
            let nseString :=
              nse.foldl (fun result elem =>
                match elem with
                  | `(namespaceSeparatorExtension| / $ns:str) =>
                    result.append ns.getString
                  | _ => result
              ) ns.getString

            return {representedNamespace := (mkIdent nseString.toName)}

          | _ => default

    def toTerm
      (ns : namespaceSeparator)
      : TSyntax `term := Unhygienic.run do
        return ← `(term| $(ns.representedNamespace))

  end namespaceSeparator

end Alloy
