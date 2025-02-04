/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/
import ThoR.Shared.Syntax
namespace Alloy
  /--
  This syntax category represents the check command from Alloy.
  For compatibility reasons the command is parsable in ThoR, but has no effect.
  -/

  declare_syntax_cat checkSyntaxIdents
  syntax ident : checkSyntaxIdents
  syntax "{" formula* "}" : checkSyntaxIdents

  declare_syntax_cat checkSyntaxButs
  syntax ("exactly")? num ident : checkSyntaxButs

  declare_syntax_cat checkSyntaxFors
  syntax num : checkSyntaxFors
  syntax ident : checkSyntaxFors
  syntax checkSyntaxButs,+ : checkSyntaxFors

  declare_syntax_cat checkSyntax
  syntax "check" checkSyntaxIdents : checkSyntax
  syntax "check" checkSyntaxIdents "for" checkSyntaxFors: checkSyntax
  syntax "check" checkSyntaxIdents "for" checkSyntaxFors "but" checkSyntaxButs : checkSyntax

end Alloy
