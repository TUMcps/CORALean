module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderMu

@[expose] public section

/-!
# The printed expansion of Halder's polynomial counts a term twice

[1, Eq. 24] prints `d β^(d+1) + (d − 1) e₁ β^d + (∑_{r=1}^{d−1} µᵣ β^(d−r+1)) − (d − 1) e_{d−1} β
− d e_d` for the polynomial (22), whose `r = 1` term `µ₁ β^d = (d − 1) e₁ β^d` is the second
term again. At `d = 2`, `λ = (1, 1)` and `β = 1` the polynomial (22) is `0`, as
`β² − 1/λᵢ = 0`, and the printed expansion is `2 + 2 + 2 − 2 − 2 = 2`.

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

open Finset


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 24] as printed fails at `d = 2`, `λ = (1, 1)`, `β = 1`. -/
theorem Ellipsoid.printed_poly_counterexample : -- --- STMT ---
    ¬ ∀ (d : ℕ) (lam : Fin d → ℝ) (β : ℝ), (∀ i, 0 < lam i) → 1 ≤ d →
      ∑ i, (β ^ 2 - 1 / lam i) * ∏ j ∈ univ.erase i, (β + 1 / lam j)
        = (d : ℝ) * β ^ (d + 1)
          + ((d : ℝ) - 1) * Ellipsoid.halderElemSymm (fun i => 1 / lam i) 1 * β ^ d
          + ∑ r ∈ Icc 1 (d - 1), Ellipsoid.halderMu lam r * β ^ (d - r + 1)
          - ((d : ℝ) - 1) * Ellipsoid.halderElemSymm (fun i => 1 / lam i) (d - 1) * β
          - (d : ℝ) * Ellipsoid.halderElemSymm (fun i => 1 / lam i) d := by -- --- PROOF ---
  intro h
  have hpos : ∀ i, 0 < (![1, 1] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have := h 2 ![1, 1] 1 hpos (by norm_num)
  simp only [one_div] at this
  -- both sides at `d = 2`, `λ = (1, 1)`, `β = 1`: `0` against `2`
  have e1 : Ellipsoid.halderElemSymm (fun i => ((![1, 1] : Fin 2 → ℝ) i)⁻¹) 1 = 2 := by
    unfold Ellipsoid.halderElemSymm
    rw [show (powersetCard 1 (univ : Finset (Fin 2))) = {{0}, {1}} from by decide,
      sum_insert (by decide), sum_singleton]
    simp
    norm_num
  have e2 : Ellipsoid.halderElemSymm (fun i => ((![1, 1] : Fin 2 → ℝ) i)⁻¹) 2 = 1 := by
    unfold Ellipsoid.halderElemSymm
    rw [show (powersetCard 2 (univ : Finset (Fin 2))) = {univ} from by decide, sum_singleton]
    simp [Fin.prod_univ_two]
  have hmu : Ellipsoid.halderMu (![1, 1] : Fin 2 → ℝ) 1 = 2 := by
    unfold Ellipsoid.halderMu
    simp only [one_div, Fintype.card_fin]
    rw [e1]
    norm_num [Ellipsoid.halderElemSymm]
  simp [Fin.sum_univ_two, Icc_self, e1, e2, hmu,
    show (univ : Finset (Fin 2)).erase 0 = {1} from by decide,
    show (univ : Finset (Fin 2)).erase 1 = {0} from by decide] at this
  norm_num at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
