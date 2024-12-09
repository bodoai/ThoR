/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy section

<alloySec> ::= alloy <name> <spec>* end

-/

alloy empty_section
end

alloy module empty_module_section
end

/-With Content to create the namespace-/
#alloy
  sig A {}
end
#check default.vars.A

#alloy
  sig A {}
end
#check default1.vars.A
