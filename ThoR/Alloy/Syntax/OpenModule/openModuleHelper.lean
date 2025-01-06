/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

import ThoR.Alloy.Syntax.alloyData
import ThoR.Alloy.Syntax.OpenModule.openModule

open Lean

namespace Alloy

namespace openModule

  /--
  Creates the Type from the name. Since the data is stored as an environment extension,
  the current environment is needed.
  -/
  def toAlloyData
    (om : openModule)
    (env : Environment)
    : Except String alloyData := do
      let alloyDataState := getAlloyData env
      let key := s!"{om.moduleToOpen.lastComponentAsString}_Data".toName
      let moduleExists : Bool := alloyDataState.contains key
      if moduleExists then
        return alloyDataState.find! key
      else
        throw s!"No module with name {key} could be found. \
        If it is not a standard module (e.g. util) try importing \
        the file containint the module"

end openModule

end Alloy
