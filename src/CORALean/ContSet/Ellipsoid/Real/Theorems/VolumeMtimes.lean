import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.Mtimes
import CORALean.ContSet.Ellipsoid.Real.Theorems.ShapeMtimes
import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A square linear map scales the volume of an ellipsoid by its determinant

For a square `M`, the volume of the image ellipsoid is `|det M|` times that of `E`: the shape
of `M E` is `M Q Mᵀ`, of determinant `(det M)² det Q`, and the volume is `V_n √det`. So a linear
map does not change ratios of volumes, which [1, Eq. 19] uses for the map `Φ` that sends
`E(Eⱼ, 0)` to the unit ball.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 19]: `vol(M E) = |det M| vol(E)`, so ratios of volumes are unchanged by `M`. -/
theorem Ellipsoid.volume_mtimes (M : Mat ℝ n n) (E : Ellipsoid n) :
    (Ellipsoid.mtimes M E).volume = ENNReal.ofReal |M.det| * E.volume := by -- --- PROOF ---
  have hS : 0 ≤ E.shape.det := by
    have : E.shape.PosSemidef := by
      unfold Ellipsoid.shape
      simpa using posSemidef_self_mul_conjTranspose E.G
    exact this.det_nonneg
  simp only [Ellipsoid.volume]
  rw [Ellipsoid.shape_mtimes, det_mul, det_mul, det_transpose, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  -- `(det M) det Q (det M) = |det M|² det Q`
  have h : M.det * E.shape.det * M.det = |M.det| ^ 2 * E.shape.det := by
    rw [sq_abs]; ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
