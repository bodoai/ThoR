/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Alloy.Syntax.Signature
import ThoR.Alloy.Syntax.Predicate

import ThoR.Alloy.Syntax.FactDecl.factDecl
import ThoR.Alloy.Syntax.OpenModule

import ThoR.Alloy.Syntax.IgnoredSyntax.ignorable

open Lean

namespace Alloy
  /--
  This syntax category specifies what can be a specification in an alloy block
  -/
  declare_syntax_cat specification
  syntax sigDecl (signatureFactDecl)? : specification
  syntax factDecl : specification
  syntax predDecl : specification
  syntax assertDecl : specification
  syntax openModule : specification

  syntax ignorable : specification

  abbrev Specification := TSyntax `specification

end Alloy
