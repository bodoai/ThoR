/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
Test if mx is called ambiguous
-/
alloy m1/mx
  sig a {}
end
alloy m2/mx
  sig a {}
end
~alloy m3/mx
  open m1/mx
  open m2/mx
  fact {
    some mx/a
  }
end

def x := ["a", "r"]
def z := x.take (x.length - 1)
def a := z.drop (x.length - 2)

#eval z
#eval a

/-
Test to import from Modules
-/
#alloy module m1
  sig a {
    r : a
  }
  fact {
    some this/a
  }
end

alloy m2/te
  open m1
  sig a {
    r : a
  }
end

#alloy m3
  open m2/te
  sig a {
    r : a
  }
  sig b {}

  fact {
    some this/a
    some m2/te/a
    some te/a
    some m1/a
    some m2/te/a<:r
    some a<:r
    some b<:this/a/r
  }

end

#create m3

/-
Import module with alias
-/
alloy m1/wewa
  sig a {
    r : a
  }
end

~alloy mx/w/a
  open m1/wewa as wowo
  sig a {
    r : a
  }
  fact {
    some wewa/a
  }
end

#alloy m2/w/a
  open m1/wewa as wowo
  sig a {
    r : a
  }
  fact {
    some wowo/a
  }
end

#create m2/w/a
#check m2.w.a.vars.wowo.a
#check m2.w.a.vars.wowo.a.r
#check m2.w.a.facts.f0
