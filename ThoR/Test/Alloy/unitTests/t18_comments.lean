/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR

alloy single/line/empty/comment
  //
end

alloy single/line/comment
  // this is a comment
end

alloy multi/line/empty/comment
  /* */
  /*

  */
end

alloy multi/line/comment
  /* this is a comment */
  /*
      this
      is
      a
      comment
  */
end
