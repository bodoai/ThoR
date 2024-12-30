/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy fact declaration

<factDecl> ::= fact [<name>] <property>

-/

alloy emptyNamelessFact
sig a {}
fact {}
end
create emptyNamelessFact

#check emptyNamelessFact.facts.f0

alloy emptyFact
sig a {}
fact factName {}
end
create emptyFact

#check emptyFact.facts.factName
