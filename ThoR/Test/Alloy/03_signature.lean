/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy signature

Signatur <sigDecl> ::= ([abstract] <mult>
  sig <name>,+
  [sigExt]
  { <fieldDecl>,* }
  { formula* }? <-- see 03a_signature_facts

-/

alloy empty_signature
  sig a {}
end
#check empty_signature.vars.a

alloy empty_signatures
  sig a,b {}
end

startTestBlock empty_signatures
  #check (empty_signatures.vars.a : ∷ set univ)
  #check (empty_signatures.vars.b : ∷ set univ)

~alloy emptySetSig
  set sig a {}
end

#alloy emptySomeSig
  some sig a {}
end

startTestBlock emptySomeSig
  #check (emptySomeSig.vars.a : ∷ some univ)

alloy emptySomeSigs
  some sig a,b {}
end

startTestBlock emptySomeSigs
  #check (emptySomeSigs.vars.a : ∷ some univ)
  #check (emptySomeSigs.vars.b : ∷ some univ)

alloy emptyLoneSig
  lone sig a {}
end

startTestBlock emptyLoneSig
  #check (emptyLoneSig.vars.a : ∷ lone univ)

alloy emptyOneSig
  one sig a {}
end

startTestBlock emptyOneSig
  #check (emptyOneSig.vars.a : ∷ one univ)

alloy abstractEmptySig
  abstract sig a {}
end

~alloy abstractSetEmptySig
  abstract set sig a {}
end

alloy abstractSomeEmptySig
  abstract some sig a {}
end

startTestBlock abstractSomeEmptySig
  #check (abstractSomeEmptySig.vars.a : ∷ some univ)
  #check_failure abstractSomeEmptySig.inheritance_facts.a

alloy abstractSomeEmptySigs
  abstract some sig a,b {}
end
startTestBlock abstractSomeEmptySigs
  #check (abstractSomeEmptySigs.vars.a : ∷ some univ)
  #check_failure abstractSomeEmptySigs.inheritance_facts.a
  #check (abstractSomeEmptySigs.vars.b : ∷ some univ)
  #check_failure abstractSomeEmptySigs.inheritance_facts.b

alloy abstractLoneEmptySig
  abstract lone sig a {}
end
startTestBlock abstractLoneEmptySig
  #check (abstractLoneEmptySig.vars.a : ∷ lone univ)
  #check_failure abstractLoneEmptySig.inheritance_facts.a

alloy abstractOneEmptySig
  abstract one sig a {}
end
startTestBlock abstractOneEmptySig
  #check (abstractOneEmptySig.vars.a : ∷ one univ)
  #check_failure abstractOneEmptySig.inheritance_facts.a
