/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file intends to test Syntax which is valid, but does nothing.
This is to create compatility with alloy code. E.g. run or check commands.
-/

alloy ignore_run
  sig a,b {}
  pred p1 {}
  run p1 for 1
end

alloy ignore_check
  sig a,b {}
  pred p1 {}
  check p1 for int
end
