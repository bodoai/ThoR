/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

#alloy letDeclTest

sig a {}
pred p1 {
  let x = a | {
    some x + x
  }
}

end
