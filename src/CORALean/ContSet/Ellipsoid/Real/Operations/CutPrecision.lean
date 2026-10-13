import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The inverse of the cut ellipsoid's shape matrix

The inverse of the shape matrix [1, Eq. 16] of the ball with a parallel cut is

  `(n − 1)/(n(1 − γ²)) · (I + (1 − nγ²)/((n − 1)γ²) · c cᵀ)`

for a unit `c`: `(I − κ c cᵀ)⁻¹ = I + κ/(1 − κ) · c cᵀ`, and `1 − κ = (n − 1)γ²/(1 − γ²)`
for `κ = (1 − nγ²)/(1 − γ²)`. `cutShape_mul_cutPrecision` says so.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inverse of [1, Eq. 16]'s shape matrix, for a unit `c`. -/
noncomputable def Ellipsoid.cutPrecision (n : ℕ) (c : Vec ℝ n) (γ : ℝ) : Mat ℝ n n :=
  (((n : ℝ) - 1) / ((n : ℝ) * (1 - γ ^ 2))) •
    (1 + ((1 - (n : ℝ) * γ ^ 2) / (((n : ℝ) - 1) * γ ^ 2)) • vecMulVec c c)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
