module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A square linear map scales the volume of an ellipsoid by its determinant

For a square `M`, the volume of the image ellipsoid is `|det M|` times that of `E`: the shape
of `M E` is `M Q Mᵀ`, of determinant `(det M)² det Q`, and the volume is `V_n √det`. So a linear
map does not change ratios of volumes, which [1, Eq. 19] uses for the map `Φ` that sends
`E(Eⱼ, 0)` to the unit ball.

## Inputs
* `M` – square matrix
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* the volume of `M E` is `|det M|` times that of `E`

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 19]: `vol(M E) = |det M| vol(E)`, so ratios of volumes are unchanged by `M`. -/
theorem Ellipsoid.volume_mtimes (M : Mat ℝ n n) (E : Ellipsoid n) : -- --- CONCL ---
    (Ellipsoid.mtimes M E).volume = ENNReal.ofReal |M.det| * E.volume := by -- --- PROOF ---
  have hS : 0 ≤ E.Q.det := E.psd.det_nonneg
  simp only [Ellipsoid.volume]
  rw [show (Ellipsoid.mtimes M E).Q = M * E.Q * Mᵀ from rfl, det_mul, det_mul, det_transpose,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  -- `(det M) det Q (det M) = |det M|² det Q`
  have h : M.det * E.Q.det * M.det = |M.det| ^ 2 * E.Q.det := by
    rw [sq_abs]; ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
