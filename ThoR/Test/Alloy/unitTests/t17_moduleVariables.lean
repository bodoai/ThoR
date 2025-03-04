/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR

alloy m1/e [exactly lol]
  sig a {
    r : lol
  }
end
~create m1

alloy m1/e/mv [exactly lol, kek]
  sig a {
    r : lol,
    q : kek
  }
end
~create m1/e/mv

alloy m1 [lol]
  sig a {
    r : lol
  }
end
~create m1/e

~alloy m1/duplicated/mv [lol, lol]
  sig a {
    r : lol
  }
end

~alloy m2
  open m1
  sig b {}
end

#alloy m3
  open m1 [b]
  sig b {}
end

#create m3

-- a set -> one b
#check m3.vars.m1.a.r
