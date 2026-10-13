module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity

@[expose] public section

/-!
# Halder's stationarity equation as a polynomial

[1, Eq. 21]: multiplying `∑ᵢ (1 − β²λᵢ)/(1 + βλᵢ)` of [1, Eq. 18] by `∏ⱼ (1 + βλⱼ)` clears
the denominators, giving `−∑ᵢ (β²λᵢ − 1) ∏_{j≠i} (βλⱼ + 1)`, the negative of the polynomial
`p_{d+1}(β)` of [1, Eq. 21]. Since `∏ⱼ (1 + βλⱼ) > 0`, the roots agree.

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 21]: [1, Eq. 18] times `∏ⱼ (1 + βλⱼ)` is `−p_{d+1}(β)`. -/
theorem Ellipsoid.halderStationarity_mul_prod (hlam : ∀ i, 0 < lam i) {β : ℝ}
    (hβ : 0 ≤ β) :
    Ellipsoid.halderStationarity lam β * ∏ j, (1 + β * lam j)
      = -∑ i, (β ^ 2 * lam i - 1)
          * ∏ j ∈ Finset.univ.erase i, (β * lam j + 1) := by -- --- PROOF ---
  unfold Ellipsoid.halderStationarity
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : 0 < 1 + β * lam i := by have := hlam i; positivity
  -- pull the `i`-th factor out of the product, leaving the product over the others
  have hP : ∏ j ∈ Finset.univ.erase i, (β * lam j + 1)
      = ∏ j ∈ Finset.univ.erase i, (1 + β * lam j) :=
    Finset.prod_congr rfl fun j _ => add_comm _ _
  rw [hP, ← Finset.mul_prod_erase Finset.univ (fun j => 1 + β * lam j) (Finset.mem_univ i)]
  generalize ∏ j ∈ Finset.univ.erase i, (1 + β * lam j) = P
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
