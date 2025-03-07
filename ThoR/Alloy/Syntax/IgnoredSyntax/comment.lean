/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

declare_syntax_cat comment
syntax "//" ident* linebreak : comment
syntax "//" linebreak : comment
syntax "/*" ident* "*/" : comment
