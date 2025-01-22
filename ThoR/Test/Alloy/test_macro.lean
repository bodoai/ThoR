import ThoR

open Lean Config

macro "startTestBlock" blockName:ident : command
  => do
    let varName ← `($(mkIdent s!"{blockName.getId}.vars".toName))
    `(variable
      ($(baseType.ident) : Type)
      [$(mkIdent `ThoR.TupleSet) $(baseType.ident)]
      [$(mkIdent `self) : $varName $(baseType.ident)]
    )
