import CORALean.ContSet.Zonotope.Real.Operations.OfEchelon
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `{[T TR], c}` with `R = T⁻¹V` is `{[T V], c}`

[1, Sec. 4.3 (new reduction)]: the reduction starts by reordering the generators as `[T V]`, `T`
invertible, and keeps `R = T⁻¹V`. The state `(T, R)` then denotes the zonotope it started from,
generator for generator, since `T(T⁻¹v) = v`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.3 (new reduction)]: at `R = T⁻¹V` the state's generators are `[T V]` themselves. -/
theorem Zonotope.ofEchelon_inv_G {n k : ℕ} (c : Vec ℝ n) (T : Mat ℝ n n) (V : Fin k → Vec ℝ n)
    (hT : IsUnit T.det) :
    (Zonotope.ofEchelon c T fun l => T⁻¹ *ᵥ V l).G
      = Fin.append (fun i a => T a i) V := by
  show Fin.append (fun i a => T a i) (fun l => T *ᵥ (T⁻¹ *ᵥ V l)) = _
  congr 1
  funext l
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
