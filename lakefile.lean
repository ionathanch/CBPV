import Lake

open Lake DSL

require MutualInduction @ git "v0.1.0"

package «CBPV» where

@[default_target]
lean_lib «CBPV» where
  globs := #[`CBPV.+]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.fieldNotation, false⟩,
    ⟨`pp.proofs, true⟩
  ]
