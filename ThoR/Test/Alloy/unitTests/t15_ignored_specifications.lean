/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file intends to test Syntax which is valid, but does nothing.
This is to create compatility with alloy code. E.g. run or check commands.

since all info is discarded you can write anything
(syntactical correct) into the commands

-/

alloy ignore_run_1
  sig a,b {}
  pred p1 {}
  run p1
end

alloy ignore_run_2
  sig a,b {}
  pred p1 {}
  run p1 for 1
end

alloy ignore_run_3
  sig a,b {}
  pred p1 {}
  run {some n: Node | self_loop[n]}
end

alloy ignore_check_1
  sig a,b {}
  pred p1 {}
  check p1
end

alloy ignore_check_2
  sig a,b {}
  pred p1 {}
  check p1 for int
end

alloy ignore_check_3
  sig a,b {}
  pred p1 {}
  check {no n: Node | self_loop[n]}
end

-- Scopes
alloy ignore_run_scope_1
  sig a,b {}
  pred p1 {}
  run {} for 5
end

alloy ignore_run_scope_2
  sig a,b {}
  pred p1 {}
  run {} for 5 but 2 A
end

alloy ignore_run_scope_3
  sig a,b {}
  pred p1 {}
  run {} for 5 but exactly 2 A
end

alloy ignore_run_scope_4
  sig a,b {}
  pred p1 {}
  run {} for 5 but 2 A, 3 B
end

alloy ignore_run_scope_5
  sig a,b {}
  pred p1 {}
  run {} for 2 A, 3 B
end

alloy ignore_run_scope_6
  sig a,b {}
  pred p1 {}
  run foo for 3 Int
end

alloy ignore_run_scope_7_unscopeable_rel
  sig a,b {}
  pred p1 {}
  run {#rel = 2}
end

--scope subtype
alloy ignore_run_subtype_scope_1
  sig a,b {}
  pred p1 {}
  run {} for 4 Plant, exactly 2 Tree
end
