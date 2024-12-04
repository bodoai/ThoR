/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Basic
import ThoR.Alloy.Syntax.Module.moduleName

open Lean

namespace Alloy

/--
Represents a module open command (module import)
-/
structure moduleOpen where
  mk :: (name : moduleName)
        (refferingName : Ident) -- the Name that is insertet in the module
        (aliasName : Ident) -- alternate name to call the module
deriving Repr


declare_syntax_cat moduleOpen
syntax "open" moduleName "[" ident "]" ("as" ident)? : moduleOpen

namespace moduleOpen

instance : Inhabited moduleOpen where
  default := {
      name := Inhabited.default,
      refferingName := mkIdent "".toName,
      aliasName := mkIdent "".toName
    }

instance : ToString moduleOpen where
  toString (mo : moduleOpen) : String :=
    s!"moduleOpen : \{
        name := {mo.name.fullNameIdentifier.getId},
        refferingName := {mo.refferingName.getId},
        alias := {mo.aliasName.getId}
      }"

def toType (mo : TSyntax `moduleOpen) : moduleOpen := Id.run do
  match mo with
    |`(moduleOpen | open $mn:moduleName [ $refName:ident ]) =>
      return {
        name := moduleName.toType mn,
        refferingName := refName,
        aliasName := refName
      }
    | `(moduleOpen | open $mn:moduleName [ $refName:ident ]
          as $aliasName:ident) =>
      return {
        name := moduleName.toType mn,
        refferingName := refName,
        aliasName := aliasName
      }

    | _ => unreachable!

end moduleOpen

end Alloy
