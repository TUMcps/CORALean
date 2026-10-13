import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStep
import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderInvSumPos
import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLamSumPos
import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityEq

/-!
# Below the fixed point of Halder's step

The step [1, Eq. 26] lowers `β > 0` exactly where the stationarity function [1, Eq. 18] is
negative: `g(β) < β` iff `∑ 1/(1+βλᵢ) < β² ∑ λᵢ/(1+βλᵢ)`.

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

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `g(β) < β` iff [1, Eq. 18] is negative at `β > 0`. -/
theorem Ellipsoid.halderStep_lt_iff [Nonempty ι] (hlam : ∀ i, 0 < lam i) {β : ℝ} (hβ : 0 < β) :
    Ellipsoid.halderStep lam β < β ↔ Ellipsoid.halderStationarity lam β < 0 := by
  unfold Ellipsoid.halderStep
  rw [Real.sqrt_lt' hβ, Ellipsoid.halderStationarity_eq,
    div_lt_iff₀ (Ellipsoid.halderLamSum_pos hlam hβ.le), sub_neg]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
