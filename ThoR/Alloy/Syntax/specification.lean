/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Alloy.Syntax.Signature
import ThoR.Alloy.Syntax.Predicate

import ThoR.Alloy.Syntax.factDecl
import ThoR.Alloy.Syntax.OpenModule

import ThoR.Alloy.Syntax.IgnoredSyntax.run
import ThoR.Alloy.Syntax.IgnoredSyntax.check

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

  syntax runSyntax : specification
  syntax checkSyntax : specification

end Alloy
