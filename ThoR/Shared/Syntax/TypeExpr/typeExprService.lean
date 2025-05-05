/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.Mutuals.mutualsService
import ThoR.Shared.Syntax.TypeExpr.typeExprHelper

open Alloy ThoR
open Lean

namespace Shared.typeExpr

  /--
  Generates a Lean term corresponding to the RelType

  to be called from outside of an alloy block
  -/
  def toRelTypeTermOutsideBlock
    (te : Shared.typeExpr)
    : Except String Term := do
      match te with
        | Shared.typeExpr.arrowExpr ae =>
          return unhygienicUnfolder
            `($(← ae.toTermOutsideBlock))

        | Shared.typeExpr.multExpr m e =>
          return unhygienicUnfolder
            `(($(mkIdent ``RelType.mk.unary_rel)
                $(m.toTerm) $(← e.toTermOutsideBlock)))

        | Shared.typeExpr.relExpr e =>
          return unhygienicUnfolder
            `(($(mkIdent ``RelType.mk.rel)
                $(← e.toTermOutsideBlock)))

end Shared.typeExpr
