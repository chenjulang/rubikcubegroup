import Lake
open Lake DSL

def extraArgs := #["-DautoImplicit=false", "-Dlinter.unusedVariables=false"]

package «rubiks-cube» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here
  moreServerArgs := extraArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
-- lake update Paperproof
-- lake exe cache get

@[default_target]
lean_lib «RubiksCube» where
  -- add any library configuration options here
