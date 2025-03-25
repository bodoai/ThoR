import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules

import ThoR.Alloy.Delab

#alloy model1
  sig a {}
  sig y {}
end
#create model1

startTestBlock model1

lemma l1 : 1=1 := by
  have h1 : [alloy| univ = univ] := by sorry
  -- TODO lookup a in AST in environment
  -- This should work: have h2 : [alloy| a = univ] := by sorry
  have h2 : [alloy| @ model1.vars.a = univ] := by sorry
  have h3 : [alloy| a = univ] := by sorry

  sorry


variable (y : ∷ set univ)
#check [alloy| all x : univ | x + y + univ = univ].eval

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
