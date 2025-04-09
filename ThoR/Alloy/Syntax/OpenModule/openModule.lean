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
  moduleVariables : List (String)
deriving Repr

declare_syntax_cat openModule
abbrev OpenModule := TSyntax `openModule
syntax
  "open" separatedNamespace
  ("[" (ident)+ "]")?
  ("as" ident)?
  : openModule

instance : Inhabited openModule where
  default :=
    {
      moduleToOpen := default,
      moduleAlias := default,
      moduleVariables := default
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
    (om : OpenModule)
    : Except String openModule := do
      match om with
        | `(openModule| open $sn:separatedNamespace) =>
          let name :=
            (← separatedNamespace.toType sn).representedNamespace.getId

          let default : openModule := default
          return { default with moduleToOpen := name}

        | `(openModule | open $sn:separatedNamespace as $mAlias:ident) =>
          let name :=
            (← separatedNamespace.toType sn).representedNamespace.getId
          let aliasName := (mAlias.getId)

          let default : openModule := default
          return { default with
              moduleToOpen := name,
              moduleAlias := aliasName
          }

        | `(openModule | open $sn:separatedNamespace [$moduleVariable:ident*]) =>
          let name :=
            (← separatedNamespace.toType sn).representedNamespace.getId
          let moduleVariableNames :=
            (moduleVariable.map
              fun mv => mv.getId.lastComponentAsString
            ).toList

          let default : openModule := default
          return { default with
              moduleToOpen := name,
              moduleVariables := moduleVariableNames
          }

        | `(openModule | open $sn:separatedNamespace [$moduleVariable:ident*] as $mAlias:ident) =>
          let name :=
            (← separatedNamespace.toType sn).representedNamespace.getId
          let moduleVariableNames :=
            (moduleVariable.map
              fun mv => mv.getId.lastComponentAsString
            ).toList
          let aliasName := (mAlias.getId)

          let default : openModule := default
          return { default with
              moduleToOpen := name,
              moduleAlias := aliasName,
              moduleVariables := moduleVariableNames
          }

        | syntx =>
            throw s!"No match implemented in \
            openModule.toType \
            for '{syntx}'"

end openModule

end Alloy
