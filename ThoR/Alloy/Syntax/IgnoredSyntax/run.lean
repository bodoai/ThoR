/-
Copyright (c) 2024 RheinMain University of Applied Sciences
Released under license as described in the file LICENSE.
Authors: s. file CONTRIBUTORS
-/

namespace Alloy
  /--
  This syntax category represents the run command from Alloy.
  For compatibility reasons the command is parsable in ThoR, but has no effect.
  -/
  declare_syntax_cat runSyntaxIdents
  syntax ident : runSyntaxIdents
  syntax "{" "}" : runSyntaxIdents

  declare_syntax_cat runSyntaxButs
  syntax num ident : runSyntaxButs

  declare_syntax_cat runSyntaxButsExactly
  syntax "exactly" num ident : runSyntaxButsExactly

  declare_syntax_cat runSyntaxFors
  syntax num : runSyntaxFors
  syntax runSyntaxButs,* : runSyntaxFors

  declare_syntax_cat runSyntax
  syntax "run" runSyntaxIdents : runSyntax
  syntax "run" runSyntaxIdents "for" runSyntaxFors : runSyntax
  syntax "run" runSyntaxIdents "for" runSyntaxFors "but" (runSyntaxButs <|> runSyntaxButsExactly) : runSyntax

end Alloy
