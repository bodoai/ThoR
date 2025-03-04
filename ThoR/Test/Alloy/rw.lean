import Lean

elab " faq_fresh_hyp_name " : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let h := Lean.mkIdent (← Lean.Core.mkFreshUserName `h)
    Lean.Elab.Tactic.evalTactic (← `(tactic| have $h : 1 + 1 = 2 := by simp))
    Lean.Elab.Tactic.evalTactic (← `(tactic| rewrite [$h:ident]))
    Lean.Elab.Tactic.evalTactic (← `(tactic| clear $h))

example : 1 + 1 = 2 := by
  faq_fresh_hyp_name
  rfl

theorem my_rw_rule : 1 + 1 = 2 := by simp

elab " my_rewrite " " @ " hyp:ident : tactic =>
  Lean.Elab.Tactic.withMainContext do
    Lean.Elab.Tactic.evalTactic (← `(tactic| rw [$(Lean.mkIdent ``my_rw_rule):ident] at $hyp:ident))

example (h : 1 + 1 = 2) : True := by
  my_rewrite @ h
  simp
