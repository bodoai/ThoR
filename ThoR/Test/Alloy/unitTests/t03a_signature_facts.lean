/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR
import ThoR.Test.Alloy.test_macro

/-
This file tests the alloy signature facts

Signatur <sigDecl> ::= ([abstract] <mult>
  sig <name>,+
  [sigExt]
  { <fieldDecl>,* }
  { formula* }?           <-- this part

-/

#alloy empty_signature_with_empty_sigFacts
  sig a {} {}
end
create empty_signature_with_empty_sigFacts
#check empty_signature_with_empty_sigFacts.vars.a

#alloy signature_with_empty_sigFacts
  sig a {
    r : a
  } {}
end
create signature_with_empty_sigFacts
#check signature_with_empty_sigFacts.vars.a

#alloy signature_with_sigFacts
  sig a {
    r : a,
    q : a
  } {
    r = q
  }
end
create signature_with_sigFacts
#check signature_with_sigFacts.vars.a
#check signature_with_sigFacts.vars.r
#check signature_with_sigFacts.vars.q
#check signature_with_sigFacts.facts.f0

/-
this (creatin two signature with relations) does not work atm.
Reason is, that Relations (r and q) must be blockwide uniqe.
an issue has already been created for this.
-/
#alloy signatures_with_sigFacts
  sig a,b {
    r : c,
    q : c
  } {
    r = q
  }
  sig c {}
end
create signatures_with_sigFacts
#check signatures_with_sigFacts.vars.a
#check signatures_with_sigFacts.vars.r
#check signatures_with_sigFacts.vars.q
#check signatures_with_sigFacts.facts.f0
