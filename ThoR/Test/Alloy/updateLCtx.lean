import Lean


elab " show_chgd_ctx " : tactic =>
  Lean.Elab.Tactic.withMainContext do

    dbg_trace "old context:"
    let ctx ← Lean.MonadLCtx.getLCtx
    ctx.forM (fun (decl : Lean.LocalDecl) => do
      let declName := decl.userName
      dbg_trace f!" local decl: name: {declName}"
    )

    -- add new hypothesis
    Lean.Elab.Tactic.evalTactic (← `(tactic| have $(Lean.mkIdent `new) : 2 = 2 := by rfl))

    Lean.Elab.Tactic.withMainContext do
      dbg_trace "new context:"
      let ctx ← Lean.MonadLCtx.getLCtx
      ctx.forM (fun (decl : Lean.LocalDecl) => do
        let declName := decl.userName
        dbg_trace f!" local decl: name: {declName}"
      )

example (old : 1 = 1) : True := by
  show_chgd_ctx
  trivial
