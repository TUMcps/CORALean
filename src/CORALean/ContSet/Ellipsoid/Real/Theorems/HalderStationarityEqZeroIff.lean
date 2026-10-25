module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity

@[expose] public section

/-!
# Halder's stationarity equation in its second form

[1, Remark 1]: the equation `∑ᵢ (1 − β²λᵢ)/(1 + βλᵢ) = 0` of [1, Eq. 18] is equivalent to
`∑ᵢ λᵢ/(1 + βλᵢ) = d/(β(β+1))`, which is [1, Eq. 20], the condition Appendix A.1 of the paper's
reference 24 reduces to. Termwise, `(1 − β²λ)/(1 + βλ) = 1 − β(β+1) λ/(1 + βλ)`.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive
* `hβ` – `0 < β`

## Conclusion
* the stationarity equation holds iff the second form does

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC), 2018.
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

/-- [1, Remark 1]: for `β > 0`, [1, Eq. 18] holds iff [1, Eq. 20] does. -/
theorem Ellipsoid.halderStationarity_eq_zero_iff (hlam : ∀ i, 0 < lam i) {β : ℝ}
    (hβ : 0 < β) : -- --- CONCL ---
    Ellipsoid.halderStationarity lam β = 0
      ↔ ∑ i, lam i / (1 + β * lam i) = Fintype.card ι / (β * (β + 1)) := by -- --- PROOF ---
  -- termwise, `(1 − β²λ)/(1 + βλ) = 1 − β(β+1) λ/(1 + βλ)`
  have hterm : Ellipsoid.halderStationarity lam β
      = Fintype.card ι - β * (β + 1) * ∑ i, lam i / (1 + β * lam i) := by
    unfold Ellipsoid.halderStationarity
    have hc : (Fintype.card ι : ℝ) = ∑ _i : ι, (1:ℝ) := by simp
    rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hlam i
    have : (0:ℝ) < 1 + β * lam i := by positivity
    field_simp
    ring
  rw [hterm, sub_eq_zero, eq_div_iff (by positivity)]
  constructor
  · intro h; rw [h]; ring
  · intro h; rw [← h]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
