import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic

/-!
# Halder's stationarity function

Minimising the volume of the outer ellipsoid `Q(β) = (1 + 1/β) Q₁ + (1 + β) Q₂` means
minimising `log det Q(β)`. With `λᵢ` the eigenvalues of `R = Q₁⁻¹ Q₂`, the first-order
condition is [1, Eq. 18]

  `∑ᵢ (1 − β² λᵢ) / (1 + β λᵢ) = 0`,

and `halderStationarity` is its left side, a function of `β` and the `λᵢ` alone. The
eigenvalues are an argument: that they are those of `Q₁⁻¹ Q₂` is `log_det_halder_eq`.

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

/-- The left side of [1, Eq. 18]: `∑ᵢ (1 − β² λᵢ) / (1 + β λᵢ)`. -/
noncomputable def Ellipsoid.halderStationarity (lam : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, (1 - β ^ 2 * lam i) / (1 + β * lam i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
