import Lake
open Lake DSL

package «chomsky» {
  moreServerArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Grammars» {
  globs := #[.submodules `Grammars] 
  moreLeanArgs := #["-DautoImplicit=false"]
}
