/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import Lean

import ThoR.Alloy.Syntax.IgnoredSyntax.comment

open Lean Lean.Elab Command Term

namespace Alloy

  declare_syntax_cat syntax_with_comments_element

  syntax str : syntax_with_comments_element
  syntax ident : syntax_with_comments_element

  /--
  A call to syntax_with_comments is like a call to syntax, except
  between every element of the syntax the comment syntax_category is added
  -/
  syntax
    (name := syntax_with_comments_stx)
    ("#")? "syntax_with_comments" (syntax_with_comments_element)* ":" ident : command

  private def evaluate
  (elements :TSyntaxArray `syntax_with_comments_element)
  (stx_cat : Ident)
  : Command
  := Unhygienic.run do

  let comment_stx ← `(stx | ($(mkIdent `comment):ident)?)

  let mut elements_as_stx : Array (TSyntax `stx) := #[comment_stx]
  for element in elements do
    match element with
      | `(syntax_with_comments_element | $str_element:str) =>
        let str_element_stx ← `(stx | $(str_element):str)
        elements_as_stx := elements_as_stx.push str_element_stx
        elements_as_stx := elements_as_stx.push comment_stx

      | `(syntax_with_comments_element | $ident_element:ident) =>
        let ident_element_stx ← `(stx | $(ident_element):ident)
        elements_as_stx := elements_as_stx.push ident_element_stx
        elements_as_stx := elements_as_stx.push comment_stx

      | _ => unreachable!

  return ← `(command | syntax $[$elements_as_stx]* : $stx_cat)

  @[command_elab syntax_with_comments_stx]
  private def syntax_with_comments_implementation : CommandElab := fun stx => do
    try
      match stx with
        | `(
            # syntax_with_comments
            $elements:syntax_with_comments_element*
            : $stx_cat:ident
          ) =>

          let s := (evaluate elements stx_cat)
          logInfo s
          elabCommand s

        | `(
            syntax_with_comments
            $elements:syntax_with_comments_element*
            : $stx_cat:ident
          ) =>

          let s := (evaluate elements stx_cat)
          elabCommand s

        | _ => return
    catch | x => throwError x.toMessageData

end Alloy


declare_syntax_cat xxxlll
#syntax_with_comments "lolkekcd" : xxxlll
def x (i : TSyntax `xxxlll) : Bool :=
  match i with
    | `(xxxlll | $[$_:comment]? lolkekcd $[$_:comment]?) => true
    | _ => false
