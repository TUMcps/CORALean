import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic

/-!
# The sum of reciprocals in Halder's iteration

The numerator `∑ᵢ 1/(1 + β λᵢ)` of the fixed-point step [1, Eq. 26], which rewrites the
stationarity condition [1, Eq. 18] as `β² ∑ λᵢ/(1+βλᵢ) = ∑ 1/(1+βλᵢ)`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `∑ᵢ 1 / (1 + β λᵢ)`, the numerator under the root of [1, Eq. 26]. -/
noncomputable def Ellipsoid.halderInvSum (lam : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, 1 / (1 + β * lam i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
