module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderLogDet
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# The derivative of the volume criterion

The derivative of `∑ᵢ log((1 + 1/β) + (1 + β) λᵢ)` is
`−(1/(β(1+β))) ∑ᵢ (1 − β²λᵢ)/(1 + βλᵢ)` ([1, Eq. 17] in the eigen-coordinates): each
summand's derivative `(λᵢ − 1/β²)/((1 + 1/β) + (1 + β)λᵢ)` is that factor times the
corresponding term of [1, Eq. 18]. The first-order condition for [1, Eq. 14] is therefore
the vanishing of [1, Eq. 18], the prefactor being nonzero.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hβ` – `0 < β`

## Conclusion
* the criterion's derivative is `−1/(β(1+β))` times the stationarity sum

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 18]: the derivative of the criterion is `−1/(β(1+β))` times the stationarity sum. -/
theorem Ellipsoid.halderLogDet_hasDerivAt (hlam : ∀ i, 0 < lam i) {β : ℝ}
    (hβ : 0 < β) : -- --- CONCL ---
    HasDerivAt (Ellipsoid.halderLogDet lam)
      (-(1 / (β * (1 + β))) * Ellipsoid.halderStationarity lam β) β := by -- --- PROOF ---
  unfold Ellipsoid.halderLogDet Ellipsoid.halderStationarity
  -- each logarithm differentiates to `(λᵢ − 1/β²)` over its argument
  have hterm : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun y => Real.log ((1 + y⁻¹) + (1 + y) * lam i))
      ((-(β ^ 2)⁻¹ + lam i) / ((1 + β⁻¹) + (1 + β) * lam i)) β := by
    intro i _
    have h1 : HasDerivAt (fun y : ℝ => (1 + y⁻¹) + (1 + y) * lam i)
        (-(β ^ 2)⁻¹ + lam i) β := by
      have := ((hasDerivAt_inv hβ.ne').const_add 1).add
        (((hasDerivAt_id β).const_add 1).mul_const (lam i))
      exact this.congr_deriv (by simp)
    exact h1.log (by have := hlam i; positivity)
  have := HasDerivAt.fun_sum hterm
  simp only [one_div]
  refine this.congr_deriv ?_
  -- and the quotient is the prefactor times the stationarity term
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hlam i
  have : (0:ℝ) < 1 + β * lam i := by positivity
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
