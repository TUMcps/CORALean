module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# An order admissible for a window and its matrix

`⌈‖r • toRealMat sys.A‖⌉₊`, no search: `timeIntervalStep_outer`'s side
condition at order `η` needs `‖r • A‖` under `η + 2`, and every `η` from this
order plus `2` up clears it outright, `reachOrder_admissible` its proof. Read
for `reach`'s floor on `η` and no further, so no tightness is claimed — a caller
wanting one closer to `[1, Alg. 1]`'s tuned choice reaches for `aux_tunedStep`.

## Inputs
* `sys` – linear system
* `r` – window width

## Output
* order admissible for the window once two is added

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order admissible for the window `r` at `sys.A` once `2` is added: every
`timeIntervalStep r η` with `η` at or above that is enclosing. -/
noncomputable def LinearSys.reachOrder (sys : LinearSys 𝕋 n) (r : ℝ) : ℕ :=
  ⌈‖r • toRealMat sys.A‖⌉₊

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
