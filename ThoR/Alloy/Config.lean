/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/-
This File contains configurable constants, implemented as get functions,
which are used to access said constants
-/
namespace Config

/-- gets the separator used for relations -/
def relationSeparator : String := "_ξ_"

/-- gets the separator used for relations -/
def signatureSeparator : String := "_φ_"

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
  namespace baseType

    /--Get the baseType as String-/
    def string : String := "ThoR_TupleSet"

    /--Get the baseType as Ident-/
    def ident : Lean.Ident := Lean.mkIdent string.toName

  end baseType

end Config
