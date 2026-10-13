import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The shape of the smallest ellipsoid containing a ball with a parallel cut

[1, Eq. 16] is the shape matrix of the smallest ellipsoid containing the unit ball `B` with the
slab `|cᵀx| ≤ γ`, `‖c‖ = 1`, `γ ∈ (0, 1/√n)` ([1, Lemma 4.3 (containment)])

  `E = n(1 − γ²)/(n − 1) · (I − (1 − nγ²)/(1 − γ²) · c cᵀ)`,

with semi-axis² `nγ²` along `c` and `n(1 − γ²)/(n − 1)` across it. The formula divides by
`n − 1` and `1 − γ²`: it is for `n ≥ 2` and `γ² < 1`.

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

/-- [1, Eq. 16]: `n(1 − γ²)/(n − 1) · (I − (1 − nγ²)/(1 − γ²) · c cᵀ)`. -/
noncomputable def Ellipsoid.cutShape (n : ℕ) (c : Vec ℝ n) (γ : ℝ) : Mat ℝ n n :=
  ((n : ℝ) * (1 - γ ^ 2) / ((n : ℝ) - 1)) •
    (1 - ((1 - (n : ℝ) * γ ^ 2) / (1 - γ ^ 2)) • vecMulVec c c)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
