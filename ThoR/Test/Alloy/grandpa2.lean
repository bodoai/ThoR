import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq
import Lean
open Lean

#alloy
module language/grandpa1 ---- Page 84, 85

abstract sig Person {
  father: lone Man,
  mother: lone Woman
  }

sig Man extends Person {
  wife: lone Woman
  }

sig Woman extends Person {
  husband: lone Man
  }

fact {
  no p: Person | p in p.^(mother+father)
  wife = ~husband
  }

assert NoSelfFather {
  no m: Man | m = m.father
  }

check NoSelfFather

pred ownGrandpa [p: Person] {
  p in p. (mother+father) .father
  }

run ownGrandpa for 4 Person

assert NoSelfGrandpa {
  no p: Person | p in p. (mother+father) .father
  }

check NoSelfGrandpa for 4 Person
end

#create language/grandpa1

startTestBlock language.grandpa1

syntax "dup" term "as" ident : tactic
macro_rules
  | `(tactic|dup $t:term as $hypothesis:ident) =>
  `(tactic|
    have $hypothesis : $t = $t := by simp)

syntax "dup_rel_r" term "as" ident : tactic
macro_rules
  | `(tactic|dup_rel_r $t:term as $hypothesis:ident) =>
  `(tactic|
    dup $t as $hypothesis
    ;
    conv at $hypothesis =>
      rhs
      simp [ThoR.HSubset.hSubset]
      simp [ThoR.Rel.subset]
      simp [ThoR.HDotjoin.hDotjoin]
      dsimp [HAdd.hAdd]
    )

syntax "dup_rel_l" term "as" ident : tactic
macro_rules
  | `(tactic|dup_rel_l $t:term as $hypothesis:ident) =>
  `(tactic|
    dup $t as $hypothesis
    ;
    conv at $hypothesis =>
      lhs
      simp [ThoR.HSubset.hSubset]
      simp [ThoR.Rel.subset]
      simp [ThoR.HDotjoin.hDotjoin]
      dsimp [HAdd.hAdd]
    )

syntax "rewrite" term "to" term "as" ident : tactic
macro_rules
  | `(tactic|rewrite $t1:term to $t2:term as $h:ident) =>
  `(tactic|
    dup_rel_r $t1 as h1
    ;
    dup_rel_l $t2 as h2
    ;
    rw [Rules.dotjoin.add.dist.r] at h1
    ;
    have $h := h2.mp ∘ h1.mp
    ;
    clear h1 h2
  )



lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p
  unfold ThoR.Quantification.Formula.eval
  intro contra
  simp [ThoR.Quantification.Formula.eval] at contra

  dup_rel_r p ⊂ p ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father))) as h1

  dup_rel_l p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father))) as h2


  -- have h1 :
  --   p ⊂ p ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father)))
  --   ↔
  --   p ⊂ p ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father)))
  -- := by simp
  -- have h2 :
  --   p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father)))
  --   ↔
  --   p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father)))
  -- := by simp

  -- conv at h1 =>
  --   rhs
  --   simp [ThoR.HSubset.hSubset]
  --   simp [ThoR.Rel.subset]
  --   simp [ThoR.HDotjoin.hDotjoin]
  --   dsimp [HAdd.hAdd]

  -- conv at h2 =>
  --   lhs
  --   simp [ThoR.HSubset.hSubset]
  --   simp [ThoR.Rel.subset]
  --   simp [ThoR.HDotjoin.hDotjoin]
  --   dsimp [HAdd.hAdd]

  -- rw [Rules.dotjoin.add.dist.r] at h1

  -- have hr := h2.mp ∘ h1.mp

  -- apply h1.mp at contra
  -- apply h2.mp at contra

  rewrite p ⊂ p ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father))) to p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father))) as hr
  clear h1 h2

  -- fact f0 : language.grandpa1.facts.f0
  -- sorry
  -- -- cases f0 with
  -- -- | intro f1 f2 =>
  -- --   apply Rules.no.elim at f1
  -- --   apply f1
  -- --   apply Rules.some.intro
  -- --   simp [ThoR.Quantification.Formula.eval] at contra
  -- --   -- dsimp [ThoR.HSubset.hSubset] at contra
  -- --   -- unfold ThoR.Rel.subset at contra
  -- --   -- simp [ThoR.HDotjoin.hDotjoin] at contra
  -- --   -- simp [HAdd.hAdd] at contra
  -- --   apply Rules.eq.subset p p at contra
  -- --   have h : p ≡ p := by apply Rules.eq.refl
  -- --   apply contra at h
  -- --   sorry
  sorry
