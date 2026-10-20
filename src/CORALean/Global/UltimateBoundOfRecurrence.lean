module

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The ultimate bound of a contracting recurrence

[1, Prop. 1]: if the W-radius satisfies `ℓ_{k+1} ≤ γ ℓ_k + ε` Eq. 17 of [1, Thm. 3] with
`γ ∈ (0, 1)`, it is ultimately bounded by `ε / (1 - γ)` Eq. 25 of [1, Prop. 1]. The paper takes
`k → ∞` in Eq. 17 to get `ℓ_∞ ≤ γ ℓ_∞ + ε`, which assumes the limit exists; it need not, and is not
needed. Unrolling gives `ℓ_k ≤ γᵏ ℓ_0 + ε / (1 - γ)` at every `k`, and so, for every `δ > 0`,
eventually `ℓ_k ≤ ε / (1 - γ) + δ`: the bound for the limit superior.

## Inputs
* `ℓ` – radius sequence
* `γ` – contraction factor
* `ε` – additive error

## Hypotheses
* `hγ0` – the factor is nonnegative
* `hγ1` – the factor is below one
* `hε` – the error is nonnegative
* `h` – each radius is at most the factor times the previous one plus the error

## Conclusion
* every radius obeys the unrolled bound and is eventually within any margin of the ultimate bound

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter


-- =======================================  MAIN THEOREM  ======================================= --

theorem ultimately_le_of_le_mul_add (ℓ : ℕ → ℝ) (γ ε : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (h : ∀ k, ℓ (k + 1) ≤ γ * ℓ k + ε) : -- --- CONCL ---
    (∀ k, ℓ k ≤ γ ^ k * ℓ 0 + ε / (1 - γ)) ∧
      ∀ δ > 0, ∀ᶠ k in atTop, ℓ k ≤ ε / (1 - γ) + δ := by -- --- PROOF ---
  have h1 : 0 < 1 - γ := by linarith
  -- unrolled: `ℓ_k ≤ γᵏ ℓ_0 + ε / (1 - γ)`
  have hk : ∀ k, ℓ k ≤ γ ^ k * ℓ 0 + ε / (1 - γ) := by
    intro k
    induction k with
    | zero => simpa using div_nonneg hε h1.le
    | succ k ih =>
      calc ℓ (k + 1) ≤ γ * ℓ k + ε := h k
        _ ≤ γ * (γ ^ k * ℓ 0 + ε / (1 - γ)) + ε := by gcongr
        _ = γ ^ (k + 1) * ℓ 0 + ε / (1 - γ) := by field_simp; ring
  refine ⟨hk, fun δ hδ => ?_⟩
  -- `γᵏ ℓ_0 → 0`
  have ht : Tendsto (fun k => γ ^ k * ℓ 0) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (ℓ 0)
  filter_upwards [(ht.eventually (gt_mem_nhds hδ))] with k hk'
  linarith [hk k]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
