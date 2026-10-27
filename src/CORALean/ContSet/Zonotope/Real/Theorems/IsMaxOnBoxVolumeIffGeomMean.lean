module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The box volume and its `n`-th root have the same maximizers

[1, Sec. IV-B, Step 3)]: over any set of nonnegative scaling factors `γ`, `γ` maximizes the volume
`2ⁿ ∏ᵢ γ(i)` of the box `⟨0, diag(γ)⟩` exactly when it maximizes `(∏ᵢ γ(i))^{1/n}`, as `x ↦ x^{1/n}`
is strictly increasing on `[0, ∞)`. That the `n`-th root is concave is not proved here.

## Inputs
* `n` – dimension
* `S` – feasible set
* `γ` – candidate point

## Hypotheses
* `hn` – dimension positive
* `hS` – feasible points nonnegative
* `hγ` – candidate lies in `S`

## Conclusion
* maximizing the box volume is the same as maximizing the geometric mean

## References

* [1] [L. Lützow, N. Kochdumper and M. Althoff. "Underapproximative Methods for the Order Reduction
      of Zonotopes". IEEE Control Systems Letters,
      2025.](../../../../../../references/2025/luetzow-lcss-underapprox-order-reduction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-B]: `γ` maximizes `2ⁿ ∏ γ(i)` over `S` iff it maximizes `(∏ γ(i))^{1/n}`. -/
theorem Zonotope.isMaxOn_boxVolume_iff_geomMean {n : ℕ} (hn : 0 < n) (S : Set (Fin n → ℝ))
    (hS : ∀ γ ∈ S, ∀ i, 0 ≤ γ i) (γ : Fin n → ℝ) (hγ : γ ∈ S) : -- --- CONCL ---
    IsMaxOn (fun γ : Fin n → ℝ => 2 ^ n * ∏ i, γ i) S γ
      ↔ IsMaxOn (fun γ : Fin n → ℝ => (∏ i, γ i) ^ (1 / (n : ℝ))) S γ := by -- --- PROOF ---
  -- both are `∀ γ' ∈ S, f γ' ≤ f γ`, and the two orders agree on nonnegative products
  have hp : ∀ γ' ∈ S, 0 ≤ ∏ i, γ' i := fun γ' h => Finset.prod_nonneg fun i _ => hS γ' h i
  have hz : (0 : ℝ) < 1 / n := by positivity
  simp only [isMaxOn_iff]
  refine forall₂_congr fun γ' h => ?_
  rw [mul_le_mul_iff_right₀ (by positivity), Real.rpow_le_rpow_iff (hp γ' h) (hp γ hγ) hz]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
