/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Alloy.SymbolTable.commandDecl
import ThoR.Alloy.SymbolTable.varDecl

namespace Alloy

  structure calledPredicate where
    mk :: (calledPredicate : commandDecl)
          (arguments : List (varDecl))

end Alloy
