/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

import Lean
import ThoR.Alloy.Config
open Lean Config

namespace delaborationService

/--
Turns an thoR representation of an ident to an alloy represetation
e.g. m1.a_φ_r to m1/a/r
-/
def switch_thoR_representation_to_alloy_representation
  (input : Ident)
  : StrLit := Id.run do

    let name := input.getId

    let components := name.components.map fun c => c.toString

    if components.isEmpty then
      return Syntax.mkStrLit "Error delaborating"

    let components_without_object := (components.take (components.length - 1))
    let objectName := components.getLast!

    let object_relation_split := objectName.splitOn relationSeparator
    let object_signaure_split := object_relation_split.map fun r => r.splitOn signatureSeparator

    let objectComponents := (object_signaure_split.join).filter fun oc => oc != "this"

    let new_components := components_without_object ++ objectComponents

    let result : String := (new_components.drop 1).foldl
      (fun res c => s!"{res}/{c}")
      (new_components.get! 0)

    return Syntax.mkStrLit result

end delaborationService
