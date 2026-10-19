module

public import CORALean.ContDynamics.Conform.Theorems.IntervalNormSmul
public import CORALean.ContDynamics.Conform.Plant
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# [1, Thm. 1]: the linear program's objective is the interval-norm cost

At `α ≥ 0`, `n^T z` with `n = [0, ∑_k ω_k σ^T G̃(I_m, t_k)]` (15) is
`∑_{k=0}^K ω_k ‖R(t_k) - ỹ(t_k)‖_{I,σ}` (13), the norm taken of the generators
`G(t_k)` of (21) — `|M diag(α)| 1 = |M| α` (32) once per block
(`intervalNorm_smul`). The center
`c` does not enter: [1, Eq. 11] moves it to the origin first, which is `n`'s zero block.

## References

* [1] M. Althoff. "Checking and Establishing Reachset Conformance in CORA 2023". In Proc. of
      the 10th International Workshop on Applied Verification of Continuous and Hybrid
      Systems (ARCH23), EPiC Series in Computing, vol. 96, pp. 9-33, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n p q : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One step's norm, split into the blocks of (20) at `M = I_m`. -/
theorem aux_step_cost (sys : Conform.Plant n p q) {ιX ιW ιV : Type} [Fintype ιX]
    [Fintype ιW] [Fintype ιV] (GX : ιX → Vec ℝ n) (αX : ιX → ℝ) (GW : ιW → Vec ℝ n)
    (αW : ιW → ℝ) (GV : ιV → Vec ℝ q) (αV : ιV → ℝ) (hαX : ∀ x, 0 ≤ αX x)
    (hαW : ∀ r, 0 ≤ αW r) (hαV : ∀ l, 0 ≤ αV l) (σ : Vec ℝ q) (k : ℕ) : -- --- CONCL ---
    Conform.intervalNorm σ (fun j => Sum.elim (Sum.elim αX fun r : Fin k × ιW => αW r.2) αV j
        • Sum.elim (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
          (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV j)
      = ∑ x, (∑ a, σ a * |((sys.C * sys.A ^ k) *ᵥ GX x) a|) * αX x
        + ∑ r, (∑ i : Fin k, ∑ a, σ a * |((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r) a|) * αW r
        + ∑ l, (∑ a, σ a * |GV l a|) * αV l := by -- --- PROOF ---
  rw [Conform.intervalNorm_smul _ _ _ fun j => by
    rcases j with (x | r) | l <;> simp [hαX, hαW, hαV]]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin k))]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1]: `n^T z` is `∑_{k ≤ K} ω_k ‖R(t_k) - ỹ(t_k)‖_{I,σ}` for `α ≥ 0`. -/
theorem Conform.Plant.lpCost_eq (sys : Conform.Plant n p q) {ιX ιW ιV : Type} [Fintype ιX]
    [Fintype ιW] [Fintype ιV] (GX : ιX → Vec ℝ n) (αX : ιX → ℝ) (GW : ιW → Vec ℝ n)
    (αW : ιW → ℝ) (GV : ιV → Vec ℝ q) (αV : ιV → ℝ) (hαX : ∀ x, 0 ≤ αX x)
    (hαW : ∀ r, 0 ≤ αW r) (hαV : ∀ l, 0 ≤ αV l) (σ : Vec ℝ q) (ω : ℕ → ℝ) (K : ℕ) : -- --- CONCL ---
    ∑ k ∈ Finset.range (K + 1), ω k * Conform.intervalNorm σ (fun j =>
        Sum.elim (Sum.elim αX fun r : Fin k × ιW => αW r.2) αV j
        • Sum.elim (Sum.elim (fun x => (sys.C * sys.A ^ k) *ᵥ GX x)
          (fun r : Fin k × ιW => (sys.C * sys.A ^ (r.1 : ℕ)) *ᵥ GW r.2)) GV j)
      = ∑ x, (∑ k ∈ Finset.range (K + 1),
            ω k * ∑ a, σ a * |((sys.C * sys.A ^ k) *ᵥ GX x) a|) * αX x
        + ∑ r, (∑ k ∈ Finset.range (K + 1),
            ω k * ∑ i : Fin k, ∑ a, σ a * |((sys.C * sys.A ^ (i : ℕ)) *ᵥ GW r) a|) * αW r
        + ∑ l, (∑ k ∈ Finset.range (K + 1), ω k * ∑ a, σ a * |GV l a|) * αV l := by -- --- PROOF ---
  simp only [aux_step_cost sys GX αX GW αW GV αV hαX hαW hαV, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  -- each block: exchange the sum over steps with the one over generators
  rw [Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.univ (α := ιX)),
    Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.univ (α := ιW)),
    Finset.sum_comm (s := Finset.range (K + 1)) (t := Finset.univ (α := ιV))]
  simp only [mul_assoc]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
