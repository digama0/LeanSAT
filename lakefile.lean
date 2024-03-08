import Lake
open Lake DSL

package «lean-sat»

@[default_target]
lean_lib LeanSAT {
  globs := #[.andSubmodules `LeanSAT]
}

/- In the command line you can run the examples with
`lake exe Examples.<whatever>`
-/
lean_exe Examples.ApproxMC
lean_exe Examples.Cadical
lean_exe Examples.CakeLPR
lean_exe Examples.GraphColoring
lean_exe Examples.PigeonHole


-- Note: `mathlib` and `std` are obtained transitively so that the versions all match up
require leancolls from git "https://github.com/JamesGallicchio/LeanColls.git" @ "main"
