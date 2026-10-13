import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.Plus
import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
import CORALean.ContSet.Ellipsoid.Real.Theorems.ShapePlus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Minimising the volume of the outer ellipsoid is minimising the log-determinant

[1, Eq. 14]: among the enclosures `Ellipsoid.plus` at the scalings `√(1 + 1/β)`, `√(1 + β)`
of [1, Eq. 11], whose shape is `Q(β) = (1 + 1/β) Q₁ + (1 + β) Q₂` (`shape_plus`), one has the
smaller volume `V_d √det Q(β)` exactly when it has the smaller `log det Q(β)`: the volume is
increasing in the determinant, and the logarithm is increasing on the positive reals.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
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

/-- [1, Eq. 14]: the volume of `plus` at `β` is at most that at `β'` iff `log det Q(β)` is. -/
theorem Ellipsoid.volume_plus_halder_le_iff {E₁ E₂ : Ellipsoid n} (h₁ : E₁.shape.PosDef)
    (h₂ : E₂.shape.PosDef) {β b : ℝ} (hβ : 0 < β) (hb : 0 < b) :
    (Ellipsoid.plus (Real.sqrt (1 + 1 / β)) (Real.sqrt (1 + β)) E₁ E₂).volume
        ≤ (Ellipsoid.plus (Real.sqrt (1 + 1 / b)) (Real.sqrt (1 + b)) E₁ E₂).volume
      ↔ Real.log (((1 + 1 / β) • E₁.shape + (1 + β) • E₂.shape).det)
        ≤ Real.log (((1 + 1 / b) • E₁.shape + (1 + b) • E₂.shape).det) := by -- --- PROOF ---
  -- the shape at each `β` is `Q(β)`, positive definite
  have hq : ∀ c : ℝ, 0 < c →
      (Ellipsoid.plus (Real.sqrt (1 + 1 / c)) (Real.sqrt (1 + c)) E₁ E₂).shape
        = (1 + 1 / c) • E₁.shape + (1 + c) • E₂.shape := by
    intro c hc
    rw [Ellipsoid.shape_plus, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hdet : ∀ c : ℝ, 0 < c → 0 < ((1 + 1 / c) • E₁.shape + (1 + c) • E₂.shape).det := by
    intro c hc
    exact ((h₁.smul (by positivity)).add (h₂.smul (by positivity))).det_pos
  have hV : 0 < Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
    have : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  unfold Ellipsoid.volume
  rw [hq β hβ, hq b hb, ENNReal.ofReal_le_ofReal_iff (by have := hdet b hb; positivity),
    mul_le_mul_iff_right₀ hV, Real.sqrt_le_sqrt_iff (hdet b hb).le,
    Real.log_le_log_iff (hdet β hβ) (hdet b hb)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
