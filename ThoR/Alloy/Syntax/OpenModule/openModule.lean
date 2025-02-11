/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Syntax.SeparatedNamespace

open Lean

/-
This file represents the opening of an alloy module.
This works by adding the AST of the modules together.
-/

namespace Alloy

structure openModule where
  moduleToOpen : Name
  moduleAlias : Name
deriving Repr

declare_syntax_cat openModule
syntax "open" separatedNamespace : openModule
syntax "open" separatedNamespace "as" ident : openModule

instance : Inhabited openModule where
  default :=
    {
      moduleToOpen := default,
      moduleAlias := default
    }

instance : ToString openModule where
  toString (om : openModule) :=
    s!"OpenModule: \{
        name := {om.moduleToOpen},
        alias := {om.moduleAlias}
      }"

namespace openModule

  /--
  Creates the Type from the syntax.
  -/
  def toType
    (om : TSyntax `openModule)
    : openModule := Id.run do
      match om with
        | `(openModule| open $sn:separatedNamespace) =>
          let name :=
            (separatedNamespace.toType sn).representedNamespace.getId
          {
            moduleToOpen := name,
            moduleAlias := default
          }

        | `(openModule | open $sn:separatedNamespace as $mAlias:ident) =>
          let name :=
            (separatedNamespace.toType sn).representedNamespace.getId
          let aliasName := (mAlias.getId)
          {
            moduleToOpen := name,
            moduleAlias := aliasName
          }

        | _ => default

end openModule

end Alloy
