/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
open Lean

declare_syntax_cat commentpart
syntax stx : commentpart
syntax term : commentpart
syntax hole : commentpart
syntax command : commentpart
syntax tactic : commentpart
syntax "//" : commentpart

declare_syntax_cat comment
syntax "//" commentpart* linebreak : comment
syntax "//" linebreak : comment
syntax "/*" commentpart* "*/" : comment
