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
  "https://github.com/leanprover-community/mathlib4.git" @ "bcd9607bce748203e813b06df9f14de82f906e98"

@[default_target]
lean_lib «RubiksCube» where
  -- add any library configuration options here
