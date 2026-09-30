import Lake
open Lake DSL

-- Release lakefile (external checkout). Pins mathlib to the commit used for the kernel logs.
package «mpup-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d46bd45325c5cdf0ecf5cee0f5ff6d6e3586eb35"

@[default_target]
lean_lib «MPUP» where

lean_lib «DiophCompression» where
