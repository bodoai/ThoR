/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import ThoR.Shared.Syntax.ArrowOp.arrowOpService
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

  /--
  Parses the given syntax to the type
  -/
  def toType
    (te : TypeExpr)
    : Except String typeExpr := do
      match te with
        | `(typeExpr | $e:expr) =>
          return typeExpr.relExpr (← expr.toType e)

        | `(typeExpr | $m:mult $e:expr) =>
          return typeExpr.multExpr (← mult.toType m) (← expr.toType e)

        | `(typeExpr | $arrowExpr:arrowOp) =>
          return typeExpr.arrowExpr (← arrowOp.toType arrowExpr)

        | syntx =>
          throw s!"No match implemented in \
          typeExprService.toType \
          for '{syntx}'"

end Shared.typeExpr
