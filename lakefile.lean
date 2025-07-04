import Lake

open Lake DSL

require "ionathanch" / "MutualInduction" @ git "main"
  from git "https://github.com/ionathanch/MutualInduction" @ "main"

package «CBPV» where

@[default_target]
lean_lib «CBPV» where
  globs := #[`CBPV.+]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
