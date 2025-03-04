import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq
import Lean
import Lean.Meta.Tactic.Intro
open Lean Lean.Elab PrettyPrinter Command Term Lean.Elab.Tactic

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
    have $hypothesis : $(mkIdent ``Iff) $t $t := by simp)

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

-- TODO
-- - fresh name for h1_new and h2_new
-- - add/remove .relation by macro

open Lean.Parser.Tactic in
elab " rewrite " rw_target:ident " to " rw_result:term  : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      if declName = rw_target.getId
      then
        -- dbg_trace f!"then: {declName} = {h1.getId}"
        let declTypeDup := mkAppN (Expr.const ``Iff []) #[declType,declType]
        let declTypeDupProof :=
          mkAppN (Expr.const ``of_eq_true []) #[
            mkAppN (Expr.const ``iff_self []) #[
              declType
            ]
          ]

        let h1_new := mkIdent `h1
        liftMetaTactic fun mvarId => do
          let mvarIdNew ← mvarId.assert h1_new.getId declTypeDup declTypeDupProof
          let (_, mvarIdNew) ← mvarIdNew.intro h1_new.getId
          return [mvarIdNew]

        Lean.Elab.Tactic.evalTactic (← `(tactic | conv at $(h1_new) =>
          rhs
          simp [ThoR.HSubset.hSubset]
          simp [ThoR.Rel.subset]
          simp [ThoR.HDotjoin.hDotjoin]
          dsimp [HAdd.hAdd]))

        let h2_new := mkIdent `h2
        Lean.Elab.Tactic.evalTactic (← `(tactic| dup_rel_l $rw_result:term as $h2_new:ident))

        Lean.Elab.Tactic.evalTactic (← `(tactic| rewrite [Rules.dotjoin.add.dist.r] at $h1_new:ident))

        Lean.Elab.Tactic.evalTactic (← `(tactic| apply (($h2_new).mp ∘ ($h1_new).mp) at $rw_target:ident))

        Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h1_new $h2_new))

lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p
  unfold ThoR.Quantification.Formula.eval
  intro contra
  simp [ThoR.Quantification.Formula.eval] at contra

  rewrite contra to p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father)))

  sorry

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
