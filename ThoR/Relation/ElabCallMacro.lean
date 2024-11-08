/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.baseType

namespace ThoR
  macro "∻" name:ident : term => `((@$name $(baseType.getIdent) _ _))
end ThoR
