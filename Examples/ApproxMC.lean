import LeanSAT

open LeanSAT

namespace Examples.ApproxMC

instance : Solver IO := Solver.Impl.DimacsCommand "cadical"
instance : Solver.ModelCount IO := Solver.Impl.ApproxMCCommand

open Encode Model.PropForm.Notation in
def main : IO Unit := do
  let x : Fin 3 := 0
  let y : Fin 3 := 1
  let z : Fin 3 := 2

  let enc : EncCNF (Literal (Fin 3)) Unit := do
    Subtype.val tseitin[ {x} ∧ {y} ∧ {z} ∨ ¬{x} ∧ ¬{y} ]

  let ((),state) := enc.run

  let res ← Solver.solve state.cnf
  IO.println res
  let res ← Solver.ModelCount.modelCount state.cnf (some <|
    [x,y,z].map state.vMap)
  IO.println res
