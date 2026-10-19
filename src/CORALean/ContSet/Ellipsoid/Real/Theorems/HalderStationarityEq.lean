module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderInvSum
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLamSum

@[expose] public section

/-!
# Halder's stationarity function as the difference of two sums

Splitting each term, `(1 − β²λᵢ)/(1 + βλᵢ) = 1/(1+βλᵢ) − β² λᵢ/(1+βλᵢ)`, writes the
left side of [1, Eq. 18] as `∑ 1/(1+βλᵢ) − β² ∑ λᵢ/(1+βλᵢ)`: the form in which its root is
the fixed point of [1, Eq. 26].

## Inputs
* `lam` – eigenvalues
* `β` – weight of the shape sum

## Hypotheses
* none

## Conclusion
* the stationarity function is `halderInvSum − β² halderLamSum`

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


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 18] as `∑ 1/(1+βλᵢ) − β² ∑ λᵢ/(1+βλᵢ)`, the rewriting of [1, Eq. 26]. -/
theorem Ellipsoid.halderStationarity_eq (lam : ι → ℝ) (β : ℝ) :
    Ellipsoid.halderStationarity lam β
      = Ellipsoid.halderInvSum lam β - β ^ 2 * Ellipsoid.halderLamSum lam β := by
  unfold Ellipsoid.halderStationarity Ellipsoid.halderInvSum Ellipsoid.halderLamSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
