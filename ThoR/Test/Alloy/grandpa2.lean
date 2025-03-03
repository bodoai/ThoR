import ThoR.Alloy
import ThoR.Test.Alloy.test_macro
import ThoR.Rules.quant
import ThoR.Rules.dotjoin
import ThoR.Rules.eq
import Lean
import Lean.Meta.Tactic.Intro
open Lean Lean.Elab Command Term Lean.Elab.Tactic

#check elabTerm
#check elabTermEnsuringType

open Lean.Elab.Tactic in
elab "custom_have " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t ← Lean.Elab.Term.elabTerm t Option.none
    let v ← Lean.Elab.Tactic.elabTermEnsuringType v (Option.some t)
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.assert n.getId t v
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

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

#check MacroM

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


elab "custom_sorry_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    let goalType := goalDecl.type
    dbg_trace f!"goal type: {goalType}"

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

elab "list_local_decls_1" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

elab "list_local_decls_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- **NEW:** Find the type.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

elab "list_local_decls_3" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
      let eq? ← Lean.Meta.isExprDefEq declType goalType -- **NEW** Check if type equals goal type.
      dbg_trace f!"+ local decl[EQUAL? {eq?}]: name: {declName}"

open Lean.Elab.Tactic in
elab "custom_let " n:ident " : " t:term " := " v:term : tactic =>
  withMainContext do
    let t1 ← ((elabTerm t) none)
  return
    -- let v ← elabTermEnsuringType v t
    -- liftMetaTactic fun mvarId => do
    --   let mvarIdNew ← mvarId.define n.getId t v
    --   let (_, mvarIdNew) ← mvarIdNew.intro1P
    --   return [mvarIdNew]

elab "fresh_name" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let h1 ← mkFreshUserName `h
    let h1 := mkIdent h1
    let h2 ← mkFreshUserName `h
    let h2 := mkIdent h2
    Lean.Elab.Tactic.evalTactic (← `(tactic| have $h1 : 1 = 1 := by rfl))
    Lean.Elab.Tactic.evalTactic (← `(tactic| have $h2 : 2 = 2 := by rfl))
--    Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h1))
    dbg_trace f!"fresh name: {h1}"
    dbg_trace f!"fresh name: {h2}"

lemma l1 : ∻ language.grandpa1.asserts.NoSelfGrandpa := by
  fresh_name
  unfold NoSelfGrandpa
  apply Rules.no.intro
  apply Rules.some.neg
  apply Rules.all.intro
  intro p
  unfold ThoR.Quantification.Formula.eval
  intro contra
  simp [ThoR.Quantification.Formula.eval] at contra

  rewrite p ⊂ p ⋈ (((∻ Person.mother) + (∻ Person.father)) ⋈ ((∻ Person.father))) to p ⊂ p ⋈ (((∻ Person.mother) ⋈ (∻ Person.father)) + ((∻ Person.father)) ⋈ ((∻ Person.father))) as hr

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
