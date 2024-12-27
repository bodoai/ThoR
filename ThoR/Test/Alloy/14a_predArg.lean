/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy predicate declaration

<predArg> ::= [disj] <name>,+ : <expr>

-/

alloy emptyPredWithArg
sig a {}
pred b [x : a] {}
end
create emptyPredWithArg

#check emptyPredWithArg.preds.b
#print emptyPredWithArg.preds.b

alloy emptyPredWithArgs
sig a {}
pred b [x,y : a] {}
end
create emptyPredWithArgs

#check emptyPredWithArgs.preds.b
#print emptyPredWithArgs.preds.b

alloy emptyPredWithArgsDisj
sig a {}
pred b [disj x,y : a] {}
end
create emptyPredWithArgsDisj

#check emptyPredWithArgsDisj.preds.b
#print emptyPredWithArgsDisj.preds.b

alloy alternateBrackets
sig a {}
pred b (x : a) {}
end
create alternateBrackets

#check alternateBrackets.preds.b
#print alternateBrackets.preds.b
