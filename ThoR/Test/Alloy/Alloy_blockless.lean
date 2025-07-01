import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules

import ThoR.Alloy.Delab

#alloy model1
  sig a {}
  sig y {}
end
#create model1

#check model1.vars.a

startTestBlock model1
#check ThoR_TupleSet
#check [alloy| univ = univ]

variable (ttt : Nat)
lemma test : 1 = 1 := by
  have h1 : ttt = 1 := by sorry
  sorry

theorem test1_2 : 1 = 1 := by
  have h1 : ttt = 1 := by sorry
  sorry

example : 1 = 1 := by
  have h1 : ttt = 1 := by sorry
  sorry

lemma test2 : ttt = 1 := by
  have h1 : ttt = ttt := by trivial
  sorry

lemma l1 : ThoR_TupleSet = ThoR_TupleSet := by
  have h1 : [alloy| univ = univ] := by sorry
  have h2 : [alloy| @ model1.vars.a = univ] := by sorry
  have h3 : [alloy| a = univ] := by sorry
  sorry


variable (y : ∷ set univ)
#check [#alloy| univ = univ]
#check [#alloy| all x : univ | x + y + univ = univ].eval

-- a -> expr.string "a"
-- declaration of: x -> formula.quantification all "x" ...
-- usage of x:
lemma l2 (y : ∷ set univ) : [alloy| all x : univ | x + y + univ = univ].eval := by
  apply Rules.all.intro; intro x
  sorry

-- Elaboration:
-- 1. Schritt:

-- [alloy| all x : univ | x + y + univ = univ] -> formula.quantification ...

-- 2. Schritt:

-- (formula.quantification ...).eval ->
-- ... (expr.string "y").eval ... (expr.string "a").eval ... ->
-- ... (Makro "y") ... (Makro "a") ... ->
-- ... y ... model1.vars.a ... ->

-- Binding:
-- - expr.string "y" -> y
-- - expr.string "a" -> model1.vars.a
