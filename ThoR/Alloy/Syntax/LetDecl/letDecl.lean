/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax.Formula.formula

open Shared
open Lean

structure letDecl where
  mk ::
    (name : Name)
    (value : formula)
    (body : List (formula))
deriving Repr, Inhabited

declare_syntax_cat letDecl
syntax "let" ident "=" formula "|" formula : letDecl
syntax "let" ident "=" formula "|" "{" formula* "}" : letDecl

abbrev LetDecl := TSyntax `letDecl
