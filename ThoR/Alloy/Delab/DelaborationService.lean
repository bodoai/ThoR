/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Alloy.Config
import ThoR.Basic
open Lean Config PrettyPrinter Delaborator SubExpr Expr

namespace delaborationService

/--
Turns an thoR representation of an ident to an alloy represetation
e.g. m1.a_φ_r to m1/a/r
-/
def switch_thoR_representation_to_alloy_representation
  (input : Ident)
  : StrLit := Id.run do

    let name := input.getId

    let componentStrings := name.components.map fun c => c.toString

    if componentStrings.isEmpty then
      return Syntax.mkStrLit "Error delaborating: Empty components"

    let componentsWithoutLast :=
      (componentStrings.take (componentStrings.length - 1))

    let lastComponentString := componentStrings.getLast!

    let split1 := lastComponentString.splitOn relationSeparator
    let split2 := split1.map fun r => r.splitOn signatureSeparator
    let filteredSplit := (split2.join).filter fun oc => oc != "this"

    let newComponents := componentsWithoutLast ++ filteredSplit

    let componentResultString : String := (newComponents.drop 1).foldl
      (fun res c => s!"{res}/{c}")
      (newComponents.get! 0)

    return Syntax.mkStrLit componentResultString

  /--
  Turns an thoR representation of an ident to a lean represetation
  e.g. m1.a_φ_r to m1.a.r
  -/
  def switch_thoR_representation_to_lean_representation
    (input : Ident)
    : Ident := Id.run do

      let name := input.getId

      let components := name.components
      let lastComponent := components.getLast!

      let lastComponentString := lastComponent.toString

      let split1 := lastComponentString.splitOn relationSeparator
      let split2 := (split1.map fun r => r.splitOn signatureSeparator)
      let filteredSplit := (split2.join).filter fun elem => elem != "this"

      let newComponents : List (Name) := filteredSplit.map fun s => s.toName

      let oldPlusNewComponents :=
        (components.take (components.length - 1)).append newComponents

      let componentResultName := Name.fromComponents oldPlusNewComponents

      return mkIdent componentResultName

end delaborationService
