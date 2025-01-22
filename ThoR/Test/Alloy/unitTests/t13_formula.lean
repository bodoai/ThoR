/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR

/-
This file tests the alloy formula

<formula> ::= ( <formula> )
| <name>
| <unLogOp> <formula>
| <unRelBoolOp> <expr>
| <formula> <binLogOp> <formula>
| if <forumla> then <formula> else <formula>
| <algExpr> <algCompareOp> <algExpr>
| <expr> <relCompareOp> <expr>
| <quant> [disj] <name>,+ : <typeExpr> | <formula>

-/

alloy referencingPred -- using name
sig a {}
pred p {}
fact {p}
end
create referencingPred

#check referencingPred.preds.p
#check referencingPred.facts.f0

alloy brackets
sig a {}
pred p {}
fact {(p)}
end
create brackets

#check brackets.preds.p
#check brackets.facts.f0

#alloy ifelseUse
sig a {}
pred p {}
fact {if p then p else p}
end
#create ifelseUse

#check ifelseUse.preds.p
#check ifelseUse.facts.f0

alloy someQuantDisj
sig a {}
pred p1 {}
pred p2 {some disj x,y : a | p1}
end
create someQuantDisj

#check someQuantDisj.preds.p1
#check someQuantDisj.preds.p2

alloy someQuant
sig a {}
pred p1 {}
pred p2 {some x,y : a | p1}
end
create someQuant

#check someQuant.preds.p1
#check someQuant.preds.p2

alloy allQuantDisj
sig a {}
pred p1 {}
pred p2 {all disj x,y : a | p1}
end
create allQuantDisj

#check allQuantDisj.preds.p1
#check allQuantDisj.preds.p2

alloy allQuant
sig a {}
pred p1 {}
pred p2 {all x,y : a | p1}
end
create allQuant

#check allQuant.preds.p1
#check allQuant.preds.p2

alloy loneQuantDisj
sig a {}
pred p1 {}
pred p2 {lone disj x,y : a | p1}
end
create loneQuantDisj

#check loneQuantDisj.preds.p1
#check loneQuantDisj.preds.p2

alloy loneQuant
sig a {}
pred p1 {}
pred p2 {lone x,y : a | p1}
end
create loneQuant

#check loneQuant.preds.p1
#check loneQuant.preds.p2

alloy oneQuantDisj
sig a {}
pred p1 {}
pred p2 {one disj x,y : a | p1}
end
create oneQuantDisj

#check oneQuantDisj.preds.p1
#check oneQuantDisj.preds.p2

alloy oneQuant
sig a {}
pred p1 {}
pred p2 {one x,y : a | p1}
end
create oneQuant

#check oneQuant.preds.p1
#check oneQuant.preds.p2

alloy noQuantDisj
sig a {}
pred p1 {}
pred p2 {no disj x,y : a | p1}
end
create noQuantDisj

#check noQuantDisj.preds.p1
#check noQuantDisj.preds.p2

alloy noQuant
sig a {}
pred p1 {}
pred p2 {no x,y : a | p1}
end
create noQuant

#check noQuant.preds.p1
#check noQuant.preds.p2

alloy noSingleQuant
sig a {}
pred p1 {}
pred p2 {no x : a | p1}
end
create noSingleQuant

#check noSingleQuant.preds.p1
#check noSingleQuant.preds.p2

alloy multiQuantDefinition
sig a {}
pred p1 {}
pred p2 {}
pred p3 {}
pred p4 {some x : a | p1}
pred p5 {some y : a | {p1 p2 p3 p4}}
end
create multiQuantDefinition

#check multiQuantDefinition.preds.p1
#check multiQuantDefinition.preds.p2
#check multiQuantDefinition.preds.p3
#check multiQuantDefinition.preds.p4
#check multiQuantDefinition.preds.p5
#print multiQuantDefinition.preds.p5
