/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOp_helper

open Alloy

namespace Shared.typeExpr

  /--
  Replaces all calls to the callables from the List `callables`
  with their respective replacement
  in the given typeExpr `te`
  -/
  def replaceCalls
    (te: typeExpr)
    (callables : List (varDecl))
    : typeExpr := Id.run do
      match te with
        | arrowExpr ae =>
          arrowExpr
            (ae.replaceCalls callables)
        | multExpr m e =>
          multExpr
            m
            (e.replaceCalls callables)
        | relExpr e =>
          relExpr
            (e.replaceCalls callables)

end Shared.typeExpr
