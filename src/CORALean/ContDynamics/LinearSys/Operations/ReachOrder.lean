import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# An order admissible for a window and its matrix

`⌈‖r • toRealMat sys.A‖⌉₊`, no search: `timeIntervalStep_outer`'s side
condition needs `‖r • A‖` under `m + 4`, and this order clears it outright,
`reachOrder_admissible` its proof. Read for `reach` and no further, so no
tightness is claimed — a caller wanting one closer to `[1, Alg. 1]`'s tuned
choice reaches for `tunedStep` directly.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order admissible for the window `r` at `sys.A`, `m` in
`timeIntervalStep r (m + 2)`'s own naming. -/
noncomputable def LinearSys.reachOrder (sys : LinearSys 𝕋 n) (r : ℝ) : ℕ :=
  ⌈‖r • toRealMat sys.A‖⌉₊

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
