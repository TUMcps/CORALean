module

public import CORALean.Global.UltimateBoundOfRecurrence

@[expose] public section

/-!
# The adaptive radius bound of the LPV estimator

[1, Thm. 3]: if the P-radii of the intersection zonotopes contract,
`ϱ_k ≤ α ϱ_{k-1} + (1 - α) ℓ_d` with `α ∈ [0, 1)` (Eq. 21a of [1, Thm. 2]), and the radii are
bounded by them, `ℓ_k ≤ γ² ϱ_k` (its Eq. 21b), then `ℓ_k ≤ γ² αᵏ ϱ₀ + γ² ℓ_d` (its Eq. 31). The
theorem writes `‖d‖²_∞` for `ℓ_d`, by [1, Remark 1]'s Eq. 3, `‖d‖_∞ = max_b ‖H_d b‖`; that is the
worst case over the box, not the peak of a particular disturbance, which can be smaller
(`LinearSysDT.peakDisturbance_counterexample`), so `ℓ_d` is what the bound is stated with. The
recursion is the one [1, Thm. 2] gives at every step (`intersectDescriptorHd_pRadius_le`, with its
block split), unrolled as in the paper's proof (its Eq. 32).

## Inputs
* `ϱ` – radius sequence
* `ℓ` – bound sequence
* `α` – contraction factor
* `γ` – scaling
* `ℓd` – disturbance level
* `k` – step

## Hypotheses
* `hα0` – contraction factor nonnegative
* `hα1` – contraction factor below one
* `hℓd` – disturbance level nonnegative
* `h21a` – radii contract
* `h21b` – bounds follow the radii

## Conclusion
* the bound at step `k` is a geometric term plus the disturbance level

## References

* [1] Y. Wang, Z. Wang, V. Puig and G. Cembrano. "Zonotopic set-membership state estimation for
      discrete-time descriptor LPV systems". IEEE Transactions on Automatic Control, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.radius_le_of_contraction (ϱ ℓ : ℕ → ℝ) (α γ ℓd : ℝ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hℓd : 0 ≤ ℓd) (h21a : ∀ k, ϱ (k + 1) ≤ α * ϱ k + (1 - α) * ℓd)
    (h21b : ∀ k, ℓ k ≤ γ ^ 2 * ϱ k) (k : ℕ) : -- --- CONCL ---
    ℓ k ≤ γ ^ 2 * α ^ k * ϱ 0 + γ ^ 2 * ℓd := by -- --- PROOF ---
  have h1 : 0 < 1 - α := by linarith
  -- Eq. 32 of [1, Thm. 3]: `ϱ_k ≤ αᵏ ϱ₀ + ℓ_d`
  have hϱ := (ultimately_le_of_le_mul_add ϱ α ((1 - α) * ℓd) hα0 hα1
    (mul_nonneg h1.le hℓd) h21a).1 k
  rw [mul_div_cancel_left₀ _ h1.ne'] at hϱ
  calc ℓ k ≤ γ ^ 2 * ϱ k := h21b k
    _ ≤ γ ^ 2 * (α ^ k * ϱ 0 + ℓd) := mul_le_mul_of_nonneg_left hϱ (sq_nonneg γ)
    _ = γ ^ 2 * α ^ k * ϱ 0 + γ ^ 2 * ℓd := by ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
