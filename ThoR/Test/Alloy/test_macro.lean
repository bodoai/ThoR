import ThoR

open Lean

macro "startTestBlock" blockName:ident : command
  => do
    let varName ← `($(mkIdent s!"{blockName.getId}.vars".toName))
    `(variable
      ($(baseType.getIdent) : Type)
      [$(mkIdent `ThoR.TupleSet) $(baseType.getIdent)]
      [$(mkIdent `self) : $varName $(baseType.getIdent)]
    )
