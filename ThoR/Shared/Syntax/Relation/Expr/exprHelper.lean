/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

/- import of the mutual data structures -/
import ThoR.Shared.Syntax.Mutuals.mutuals

import ThoR.Alloy.Syntax.SeparatedNamespace.separatedNamespace

open Alloy

namespace Shared.expr
  def isString (e : expr) : Bool :=
    match e with
      | expr.string _ => true
      | _ => false

  def isCallFromOpen (e : expr) : Bool :=
    match e with
      | expr.callFromOpen _ => true
      | _ => false

  def getCalledFromOpenData (e : expr) : separatedNamespace :=
    match e with
      | expr.callFromOpen data => data
      | _ => panic! s!"Tried to get callFromOpenData from expr {e}"

  def getStringData (e : expr) : String :=
    match e with
      | expr.string data => data
      | _ => panic! s!"Tried to get String data from expr {e}"

  def getStringExpr (e:expr) : String :=
      match e with
        | expr.string s => s
        | _ => default

end Shared.expr
