
import ThoR.Shared.Syntax.Constant.constant
import Lean
open Lean

namespace Shared.constant
  /--
  Generates a Lean term corosponding with the type
  -/
  def fromTerm
    (c : Term)
    : Except Unit constant := do
    match c with
      | `(univ) => return constant.univ
      | `(iden) => return constant.iden
      | `(none) => return constant.none
      | _ => throw Unit.unit

end Shared.constant
