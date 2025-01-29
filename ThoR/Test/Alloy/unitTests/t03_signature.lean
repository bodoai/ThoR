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
create empty_signature
#check empty_signature.vars.a

alloy empty_signatures
  sig a,b {}
end
create empty_signatures

startTestBlock empty_signatures
  #check (empty_signatures.vars.a : ∷ set univ)
  #check (empty_signatures.vars.b : ∷ set univ)

alloy empty_signatures_extendedIdent_names
  sig alloy,def {}
end
create empty_signatures_extendedIdent_names
startTestBlock empty_signatures_extendedIdent_names
  #check (empty_signatures_extendedIdent_names.vars.alloy : ∷ set univ)
  #check (empty_signatures_extendedIdent_names.vars.def : ∷ set univ)

--does not work in alloy but in ThoR atm
~alloy emptySetSig
  set sig a {}
end
create emptySetSig

#alloy emptySomeSig
  some sig a {}
end
create emptySomeSig

startTestBlock emptySomeSig
  #check (emptySomeSig.vars.a : ∷ some univ)

alloy emptySomeSigs
  some sig a,b {}
end
create emptySomeSigs

startTestBlock emptySomeSigs
  #check (emptySomeSigs.vars.a : ∷ some univ)
  #check (emptySomeSigs.vars.b : ∷ some univ)

alloy emptyLoneSig
  lone sig a {}
end
create emptyLoneSig

startTestBlock emptyLoneSig
  #check (emptyLoneSig.vars.a : ∷ lone univ)

alloy emptyOneSig
  one sig a {}
end
create emptyOneSig

startTestBlock emptyOneSig
  #check (emptyOneSig.vars.a : ∷ one univ)

alloy abstractEmptySig
  abstract sig a {}
end

--does not work in alloy but in ThoR atm
~alloy abstractSetEmptySig
  abstract set sig a {}
end

alloy abstractSomeEmptySig
  abstract some sig a {}
end
create abstractSomeEmptySig

startTestBlock abstractSomeEmptySig
  #check (abstractSomeEmptySig.vars.a : ∷ some univ)
  #check_failure abstractSomeEmptySig.inheritance_facts.a

alloy abstractSomeEmptySigs
  abstract some sig a,b {}
end
create abstractSomeEmptySigs

startTestBlock abstractSomeEmptySigs
  #check (abstractSomeEmptySigs.vars.a : ∷ some univ)
  #check_failure abstractSomeEmptySigs.inheritance_facts.a
  #check (abstractSomeEmptySigs.vars.b : ∷ some univ)
  #check_failure abstractSomeEmptySigs.inheritance_facts.b

alloy abstractLoneEmptySig
  abstract lone sig a {}
end
create abstractLoneEmptySig

startTestBlock abstractLoneEmptySig
  #check (abstractLoneEmptySig.vars.a : ∷ lone univ)
  #check_failure abstractLoneEmptySig.inheritance_facts.a

alloy abstractOneEmptySig
  abstract one sig a {}
end
create abstractOneEmptySig

startTestBlock abstractOneEmptySig
  #check (abstractOneEmptySig.vars.a : ∷ one univ)
  #check_failure abstractOneEmptySig.inheritance_facts.a
