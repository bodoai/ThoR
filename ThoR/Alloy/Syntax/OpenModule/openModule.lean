/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

open Lean

/-
This file represents the opening of an alloy module.
This works by adding the AST of the modules together.
-/

namespace Alloy

structure openModule where
  moduleToOpen : Name
deriving Repr

declare_syntax_cat openModule
syntax "open" ident : openModule

instance : Inhabited openModule where
  default := {moduleToOpen := default}

instance : ToString openModule where
  toString (om : openModule) := s!"OpenModule: \{ name := {om.moduleToOpen} }"

namespace openModule

  /--
  Creates the Type from the syntax.
  -/
  def toType
    (om : TSyntax `openModule)
    : openModule := Id.run do
      match om with
        | `(openModule| open $identifier:ident) =>
          let name := identifier.getId
          {moduleToOpen := name}

        | _ => default

end openModule

end Alloy
