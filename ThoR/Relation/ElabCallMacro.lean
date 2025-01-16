/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.Config
open Config

namespace ThoR
  macro "∻" name:ident : term => `((@$name $(baseType.ident) _ _))
end ThoR
