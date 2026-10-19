module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStep
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderInvSumPos
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLamSumPos
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderStationarityEq

@[expose] public section

/-!
# Above the fixed point of Halder's step

The step [1, Eq. 26] raises `β` exactly where the stationarity function [1, Eq. 18] is
positive: `β < g(β)` iff `β² ∑ λᵢ/(1+βλᵢ) < ∑ 1/(1+βλᵢ)`, which is
`halderStationarity_eq` read as a sign. With the two companions it makes the fixed point
of `g` the root of [1, Eq. 18], which is [1, Thm. 3]'s limit.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hβ` – `0 ≤ β`

## Conclusion
* `β` is below its step iff the stationarity function is positive

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

/-- `β < g(β)` iff [1, Eq. 18] is positive at `β ≥ 0`. -/
theorem Ellipsoid.lt_halderStep_iff [Nonempty ι] (hlam : ∀ i, 0 < lam i) {β : ℝ} (hβ : 0 ≤ β) :
    β < Ellipsoid.halderStep lam β ↔ 0 < Ellipsoid.halderStationarity lam β := by
  unfold Ellipsoid.halderStep
  rw [Real.lt_sqrt hβ, Ellipsoid.halderStationarity_eq,
    lt_div_iff₀ (Ellipsoid.halderLamSum_pos hlam hβ), sub_pos]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
