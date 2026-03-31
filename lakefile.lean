import Lake

open Lake DSL

require "ionathanch" / "MutualInduction" @ git "main"

package «CBPV» where

@[default_target]
lean_lib «CBPV» where
  globs := #[`CBPV.+]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩,
    ⟨`experimental.module, true⟩
  ]
