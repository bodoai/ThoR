/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

#alloy letDeclTest1

sig a {
  r: some b
}
sig b {}

pred p1 {
  let x = a | {
    some x + x
  }
}
end

#create letDeclTest1

#alloy letDeclTest2

sig a {
  r: b
}

sig x extends a {}

sig b {
  q: a
}

sig c {}

fact {
  let y=a | {
    y.r = b
    x.r = b
  }
}
end
