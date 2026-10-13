import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLamSum

/-!
# Halder's denominator is positive

For positive `λᵢ` and `β ≥ 0`, `∑ λᵢ/(1+βλᵢ) > 0`, so the quotient under the root of
the fixed-point step [1, Eq. 26] is defined.

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

/-- `∑ᵢ λᵢ/(1+βλᵢ)` is positive at `β ≥ 0` when every `λᵢ` is. [1, Eq. 26] -/
theorem Ellipsoid.halderLamSum_pos [Nonempty ι] (hlam : ∀ i, 0 < lam i) {β : ℝ} (hβ : 0 ≤ β) :
    0 < Ellipsoid.halderLamSum lam β := by
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  have := hlam i
  exact div_pos this (by positivity)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
