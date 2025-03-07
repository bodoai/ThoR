/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Basic

namespace Shared

  /--
  This inductive type represents an alloy constant
  -/
  inductive constant where
    | none
    | univ
    | iden
  deriving Repr

  instance : ToString constant where
    toString :  constant -> String
      | constant.none => "none"
      | constant.iden => "iden"
      | constant.univ => "univ"

  instance : BEq constant where
    beq : constant -> constant -> Bool
      | constant.univ, constant.univ => true
      | constant.iden, constant.iden => true
      | constant.none, constant.none => true
      | _, _ => false

  instance : Inhabited constant where
    default := constant.none

end Shared
