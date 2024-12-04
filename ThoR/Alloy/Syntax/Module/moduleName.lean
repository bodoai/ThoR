/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic

open Lean

namespace Alloy

/--
Represents a module name
-/
structure moduleName where
  mk :: (fullNameIdentifier: Ident)
deriving Repr

declare_syntax_cat moduleName
declare_syntax_cat moduleNameExtension
syntax "/" ident : moduleNameExtension
syntax ident (moduleNameExtension)* : moduleName

instance : Inhabited moduleName where
  default := {
      fullNameIdentifier := mkIdent "".toName
    }

namespace moduleName

  def toType (mn : TSyntax `moduleName) : moduleName := Id.run do
    match mn with
      | `(moduleName| $i1:ident) =>
        return {fullNameIdentifier := i1}
      | `(moduleName| $i1:ident $extension:moduleNameExtension*) =>
        let mut fullName := i1.getId
        for e in extension do
          match e with
            | `(moduleNameExtension| / $eIdent:ident) =>
              let comps := eIdent.getId.components
              for comp in comps do
                fullName := fullName.append (comp)

            | _ => unreachable!

        return {fullNameIdentifier := (mkIdent fullName)}

      | _ => unreachable!

end moduleName

end Alloy
