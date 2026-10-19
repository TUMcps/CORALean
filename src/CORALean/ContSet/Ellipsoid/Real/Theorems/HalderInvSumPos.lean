module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderInvSum

@[expose] public section

/-!
# Halder's numerator is positive

For positive `λᵢ` and `β ≥ 0`, `∑ 1/(1+βλᵢ) > 0`, so the root of the fixed-point step
[1, Eq. 26] is of a positive number.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hβ` – `0 ≤ β`

## Conclusion
* the sum `∑ 1/(1+βλᵢ)` is positive

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

/-- `∑ᵢ 1/(1+βλᵢ)` is positive at `β ≥ 0` when every `λᵢ` is. [1, Eq. 26] -/
theorem Ellipsoid.halderInvSum_pos [Nonempty ι] (hlam : ∀ i, 0 < lam i) {β : ℝ} (hβ : 0 ≤ β) :
    0 < Ellipsoid.halderInvSum lam β := by
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  have := hlam i
  exact one_div_pos.2 (by positivity)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
