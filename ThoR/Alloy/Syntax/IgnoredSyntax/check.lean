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
  syntax num ident : checkSyntaxButs

  declare_syntax_cat checkSyntaxButsExactly
  syntax "exactly" num ident : checkSyntaxButsExactly

  declare_syntax_cat checkSyntax
  syntax "check" checkSyntaxIdents : checkSyntax
  syntax "check" checkSyntaxIdents "for" checkSyntaxIdents: checkSyntax
  syntax "check" checkSyntaxIdents "for" checkSyntaxIdents "but" (checkSyntaxButs <|> checkSyntaxButsExactly): checkSyntax

end Alloy
