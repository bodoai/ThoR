import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq
import Lean
import Lean.Meta.Tactic.Intro
open Lean Lean.Elab Command Term Lean.Elab.Tactic

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← Lean.Elab.Term.elabTerm t Option.none
    let v ← Lean.Elab.Tactic.elabTermEnsuringType v (Option.some t)
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

alloy
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

create language/grandpa1

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

-- #check Lean.Parser.Tactic.locationHyp
-- #check TSyntax [`Lean.Parser.Tactic.locationWildcard, `Lean.Parser.Tactic.locationHyp]
-- #check mkIdent
-- #check Lean.Parser.Tactic.location

-- #check Syntax.node1 SourceInfo.none `Lean.Parser.Tactic.location (
--           Syntax.node1 SourceInfo.none `Lean.Parser.Tactic.locationHyp (
--             mkIdent "abc".toName))


-- instance : Coe (Ident) (TSyntax [`Lean.Parser.Tactic.locationWildcard, `Lean.Parser.Tactic.locationHyp]) where
--   coe s := ⟨s.raw⟩
-- #check Lean.Parser.Tactic.location

open Lean.Parser.Tactic in
elab " rewrite " t1:term " to " t2:term " as " h:ident : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let h1 := mkIdent <| ← mkFreshUserName `h
    let h2 := mkIdent <| ← mkFreshUserName `h
    Lean.Elab.Tactic.evalTactic (← `(tactic| dup_rel_r $t1:term as $h1:ident))
    Lean.Elab.Tactic.evalTactic (← `(tactic| dup_rel_l $t2:term as $h2:ident))
    Lean.Elab.Tactic.evalTactic (← `(tactic| rewrite [Rules.dotjoin.add.dist.r] at $h1:ident))
    Lean.Elab.Tactic.evalTactic (← `(tactic| try have $h := ($h2).mp ∘ ($h1).mp))
    Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h1))
    Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h2))
    -- dbg_trace f!"fresh name: {h1}"

lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p
  unfold ThoR.Quantification.Formula.eval
  intro contra
  simp [ThoR.Quantification.Formula.eval] at contra

  rewrite p ⊂ p ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father))) to p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father))) as hr
  apply hr at contra

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
