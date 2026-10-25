module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# Halder's polynomial divided by the product of the eigenvalues

[1, Eq. 22]: dividing the polynomial `p_{d+1}(β) = ∑ᵢ (β²λᵢ − 1) ∏_{j≠i} (βλⱼ + 1)` of
[1, Eq. 21] by `∏ⱼ λⱼ` turns it into `∑ᵢ (β² − 1/λᵢ) ∏_{j≠i} (β + 1/λⱼ)`: for each `i`,
`(β²λᵢ − 1) = λᵢ (β² − 1/λᵢ)` and `βλⱼ + 1 = λⱼ (β + 1/λⱼ)`, and the `λ`s multiply to the
product.

## Inputs
* `β` – weight of the shape sum

## Hypotheses
* `hlam` – every `λᵢ` positive

## Conclusion
* the polynomial over `∏ λⱼ` equals the sum of products

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {lam : ι → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 22]: `p_{d+1}(β) / ∏ λⱼ = ∑ᵢ (β² − 1/λᵢ) ∏_{j≠i} (β + 1/λⱼ)`. -/
theorem Ellipsoid.halder_poly_div_prod (hlam : ∀ i, 0 < lam i) (β : ℝ) : -- --- CONCL ---
    ∑ i, (β ^ 2 - 1 / lam i) * ∏ j ∈ Finset.univ.erase i, (β + 1 / lam j)
      = (∑ i, (β ^ 2 * lam i - 1) * ∏ j ∈ Finset.univ.erase i, (β * lam j + 1))
        / ∏ j, lam j := by -- --- PROOF ---
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := (hlam i).ne'
  -- `∏_{j≠i} (βλⱼ + 1) = (∏_{j≠i} λⱼ) ∏_{j≠i} (β + 1/λⱼ)`
  have hprod : ∏ j ∈ Finset.univ.erase i, (β * lam j + 1)
      = (∏ j ∈ Finset.univ.erase i, lam j) * ∏ j ∈ Finset.univ.erase i, (β + 1 / lam j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have := (hlam j).ne'
    field_simp
  have hPne : ∏ j ∈ Finset.univ.erase i, lam j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => (hlam j).ne'
  rw [hprod, ← Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ i)]
  generalize ∏ j ∈ Finset.univ.erase i, lam j = P at hPne ⊢
  generalize ∏ j ∈ Finset.univ.erase i, (β + 1 / lam j) = Q
  field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
