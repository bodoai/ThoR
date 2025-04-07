/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.FactDecl.factDecl

open Lean

namespace Alloy

  /--
  A type representation of an signature fact declaration. It is projected on `fact declaration`
  -/
  def signatureFactDecl := factDecl
  deriving Repr, Inhabited

  /--
  A syntax repreaentation of an fact declaration.
  -/
  declare_syntax_cat signatureFactDecl
  abbrev SignatureFactDecl := TSyntax `signatureFactDecl
  syntax property : signatureFactDecl

end Alloy
