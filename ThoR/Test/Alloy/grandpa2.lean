import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq
import Lean
import Lean.Meta.Tactic.Intro
open Lean Lean.Elab PrettyPrinter Command Term Lean.Elab.Tactic

#check delab

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
    have $hypothesis : $t ↔ $t := by simp)

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

#check mkFreshUserName
#check mkAppN

#check Expr.const ``Iff.intro

lemma l7 (Q : Prop) : Iff Q Q := of_eq_true (iff_self Q)

#check mkAppN (Expr.const ``Iff [])

#print l7
#check of_eq_true
#check iff_self


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
--        dbg_trace f!"declType: {declType}"
        -- dbg_trace f!"declType': {declTypeDup}"

        -- let h1_new := mkIdent `h1
        -- liftMetaTactic fun mvarId => do
        --   let mvarIdNew ← mvarId.assert h1_new.getId declTypeDup declTypeDupProof
        --   let (_, mvarIdNew) ← mvarIdNew.intro h1_new.getId
        --   return [mvarIdNew]

        -- Lean.Elab.Tactic.evalTactic (← `(tactic | conv at $(h1_new) =>
        --   rhs
        --   simp [ThoR.HSubset.hSubset]
        --   simp [ThoR.Rel.subset]
        --   simp [ThoR.HDotjoin.hDotjoin]
        --   dsimp [HAdd.hAdd]))

        -- let h2_new := mkIdent `h2
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| dup_rel_l $rw_result:term as $h2_new:ident))

        -- Lean.Elab.Tactic.evalTactic (← `(tactic| rewrite [Rules.dotjoin.add.dist.r] at $h1_new:ident))

        -- let h3_new := mkIdent `h3
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| try have $h3_new := ($h2_new).mp ∘ ($h1_new).mp))

        -- Lean.Elab.Tactic.evalTactic (← `(tactic| apply $h3_new at $rw_target:ident))

--        Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h1_new $h2_new $h3_new))

        -- let h2 := mkIdent <| ← mkFreshUserName `h
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| dup_rel_r (($declType':term) $(mkIdent `ThoR_TupleSet)) as $h1:ident))
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| have $h1:ident : (($declType':term))))
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| dup_rel_l $t2:term as $h2:ident))
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| rewrite [Rules.dotjoin.add.dist.r] at $h1:ident))
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| try have $h := ($h2).mp ∘ ($h1).mp))
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h1))
        -- Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h2))
      -- else dbg_trace f!"else: {declName} != {h1.getId}"
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

  rewrite contra to p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father)))



--  apply hr at contra

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
