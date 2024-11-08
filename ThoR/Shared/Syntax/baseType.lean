/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
/-
`ThoR.Relation` models the concept "relation" as algebraic structure. i.e.
there exists a carrier set (resp. carrier type) which has to be
named.

`ThoR.Alloy` is based on `ThoR.Relation`. As Alloy specifications do not
explicitly name the underlying carrier set, specifications in `ThoR.Alloy`
also do not name the underlying carrier set.

Consequently, the carrier set has to be specified in the transformation
from Alloy specifications to ThoR expressions. `baseType` is the default name for this carrier set which is used wherever the name of the carrier set has to be specified
in the transformation from Alloy specifications to ThoR expressions.
-/
open Lean

namespace baseType

  /--
  Gets the 'baseType' Ident
  -/
  def getIdent : Ident := mkIdent `ThoR_TupleSet

end baseType
