module

public import CORALean.ContSet.Zonotope.Real.Theorems.SubsetOfCert
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Order reduction with a certified Hausdorff bound

`[1, Prop. 6]`: a reduced zonotope `⟨x̄, X_red⟩` with `X = X_red Γ₀`,
`X_red = X Γ₁ + Δ`, `‖[Γ₀, Γ₁]‖∞ ≤ 1` and `‖Δ‖∞ ≤ δ` (`[1, Prop. 6, Eq. 42]`) contains
`⟨x̄, X⟩` and is within `δ` of it in the Hausdorff distance of the supremum norm. The first is
`[1, Thm. 3]` at `β = 0`. For the second, a point `x̄ + X_red α` has the point
`x̄ + X (Γ₁ α)` of the original at distance `‖Δ α‖∞ ≤ δ`. What is proved is the bound at
any feasible point, so at the optimum `δ*` in particular; `0 ≤ δ` is automatic from
`‖Δ‖∞ ≤ δ` in any positive dimension and is assumed for `n = 0`.

## Inputs
* `Z` – original zonotope
* `Zr` – reduced zonotope
* `Γ₀` – coefficient matrix of the original
* `Γ₁` – coefficient matrix of the reduced
* `Δ` – residual generators
* `δ` – distance bound

## Hypotheses
* `hc` – centers agree
* `hδ` – bound nonnegative
* `h₀` – original generators expressed through the reduced
* `h₁` – reduced generators expressed through the original
* `hn₀` – first row sums at most one
* `hn₁` – second row sums at most one
* `hΔ` – residual sums at most `δ`

## Conclusion
* the original lies in the reduced one within distance `δ`

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC), 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.hausdorffDist_le_of_reduce_cert (Z Zr : Zonotope (Vec ℝ n)) (hc : Zr.c = Z.c)
    (Γ₀ : Mat ℝ Zr.h Z.h) (Γ₁ : Mat ℝ Z.h Zr.h) (Δ : Fin Zr.h → Vec ℝ n) (δ : ℝ) (hδ : 0 ≤ δ)
    (h₀ : ∀ j, Z.G j = ∑ k, Γ₀ k j • Zr.G k) (h₁ : ∀ k, Zr.G k = ∑ j, Γ₁ j k • Z.G j + Δ k)
    (hn₀ : ∀ k, ∑ j, |Γ₀ k j| ≤ 1) (hn₁ : ∀ j, ∑ k, |Γ₁ j k| ≤ 1)
    (hΔ : ∀ i, ∑ k, |Δ k i| ≤ δ) : -- --- CONCL ---
    Z.construct ⊆ Zr.construct ∧
      Metric.hausdorffDist Z.construct Zr.construct ≤ δ := by -- --- PROOF ---
  have hsub : Z.construct ⊆ Zr.construct :=
    Zonotope.construct_subset_of_cert Z Zr Γ₀ 0 h₀ (by simp [hc]) (by simpa using hn₀)
  refine ⟨hsub, Metric.hausdorffDist_le_of_mem_dist hδ (fun x hx => ⟨x, hsub hx, by simpa⟩) ?_⟩
  -- `x̄ + X_red α` is within `‖Δ α‖∞` of `x̄ + X (Γ₁ α)`
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨Z.c + ∑ j, (∑ k, Γ₁ j k * a k) • Z.G j, ⟨fun j => ∑ k, Γ₁ j k * a k, fun j => ?_, rfl⟩,
    ?_⟩
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans (hn₁ j))
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (ha k)
  · have hdiff : Zr.c + ∑ k, a k • Zr.G k - (Z.c + ∑ j, (∑ k, Γ₁ j k * a k) • Z.G j)
        = ∑ k, a k • Δ k := by
      simp only [h₁, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
        Finset.sum_smul, hc]
      rw [Finset.sum_comm (f := fun k j => (a k * Γ₁ j k) • Z.G j)]
      simp only [mul_comm (a _)]
      abel
    rw [dist_eq_norm, hdiff, pi_norm_le_iff_of_nonneg hδ]
    intro i
    rw [Finset.sum_apply, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => ?_).trans (hΔ i))
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
