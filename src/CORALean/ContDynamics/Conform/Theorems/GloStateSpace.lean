module

public import CORALean.ContDynamics.Conform.Definitions.Glo
public import CORALean.ContDynamics.Conform.Theorems.ProdJacSucc
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# [1, Cor. 1]: the GLO approximation of a state-space model

Linearized along a simulated reference — `x̄ₖ₊₁ = f(x̄ₖ, ūₖ)`, `ȳₖ = g(x̄ₖ, ūₖ)` (11a) —
with Jacobians `Aₖ, Bₖ, Cₖ, Dₖ` and remainders `l_x,ₖ`, `l_y,ₖ` (12)-(13), the output
is `τ̄ₖ + ēₖ`: `C̄ₖ = Cₖ ∏_{l=1}^k A_{k-l}` (11b), `D̄ₖ,ᵢ = Cₖ ∏_{l=1}^{k-i-1} A_{k-l} Bᵢ`
for `i < k` and `D̄ₖ,ₖ = Dₖ` (11c), `ēₖ = Cₖ ∑_{j<k} ∏_{l=1}^{k-j-1} A_{k-l} l_x,ⱼ + l_y,ₖ` — the
recursion inserted into itself, as printed. That the remainders lie in `L̂_x`, `L̂_y` comes
from the Taylor bounds of the conservative-polynomialization paper the corollary cites, so
it is the hypothesis here; `Êₖ` is the set-based evaluation of `ēₖ` over them, and [1, Thm. 1]
(`reachSetOfExact_subset`) gives the reachable set. A linear model has `l = 0` and so `ē = 0`.

## Inputs
* `x` – states
* `xb` – reference states
* `u` – inputs
* `ub` – reference inputs
* `y` – outputs
* `yb` – reference outputs
* `A` – state Jacobians
* `B` – input Jacobians of the state
* `C` – state-to-output Jacobians
* `D` – feedthrough Jacobians
* `lx` – state remainders
* `ly` – output remainders
* `k` – step

## Hypotheses
* `hx` – the state linearization holds
* `hy` – the output linearization holds

## Conclusion
* the output equals the linearization along the reference plus the remainder terms

## References

* [1] [L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE Transactions on
      Automatic Control,
      2026.](../../../../../references/2026/luetzow-tac-reachset-conformant-identification.md)
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

/-- The state deviation, unrolled. -/
private theorem aux_dev_unroll (x xb : ℕ → Vec ℝ n) (u ub : ℕ → Vec ℝ p) (A : ℕ → Mat ℝ n n)
    (B : ℕ → Mat ℝ n p) (lx : ℕ → Vec ℝ n)
    (hx : ∀ k, x (k + 1) = xb (k + 1) + A k *ᵥ (x k - xb k) + B k *ᵥ (u k - ub k) + lx k)
    (k : ℕ) : -- --- CONCL ---
    x k - xb k = Conform.prodJac A k k *ᵥ (x 0 - xb 0)
      + ∑ i ∈ Finset.range k, Conform.prodJac A k (k - i - 1) *ᵥ
          (B i *ᵥ (u i - ub i) + lx i) := by -- --- PROOF ---
  induction k with
  | zero => simp [Conform.prodJac]
  | succ k ih =>
    rw [hx k, Finset.sum_range_succ, show k + 1 - k - 1 = 0 by omega, Conform.prodJac_succ]
    have hsum : ∑ i ∈ Finset.range k, Conform.prodJac A (k + 1) (k + 1 - i - 1) *ᵥ
          (B i *ᵥ (u i - ub i) + lx i)
        = A k *ᵥ ∑ i ∈ Finset.range k, Conform.prodJac A k (k - i - 1) *ᵥ
          (B i *ᵥ (u i - ub i) + lx i) := by
      rw [mulVec_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show k + 1 - i - 1 = (k - i - 1) + 1 by omega, Conform.prodJac_succ, ← mulVec_mulVec]
    rw [hsum, ih, ← mulVec_mulVec]
    simp only [Conform.prodJac, List.range_zero, List.map_nil, List.prod_nil, one_mulVec,
      mulVec_add]
    abel


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 1]: the output is `τ̄ₖ + ēₖ` with (11b)-(11c). -/
theorem Conform.glo_stateSpace (x xb : ℕ → Vec ℝ n) (u ub : ℕ → Vec ℝ p) (y yb : ℕ → Vec ℝ q)
    (A : ℕ → Mat ℝ n n) (B : ℕ → Mat ℝ n p) (C : ℕ → Mat ℝ q n) (D : ℕ → Mat ℝ q p)
    (lx : ℕ → Vec ℝ n) (ly : ℕ → Vec ℝ q)
    (hx : ∀ k, x (k + 1) = xb (k + 1) + A k *ᵥ (x k - xb k) + B k *ᵥ (u k - ub k) + lx k)
    (hy : ∀ k, y k = yb k + C k *ᵥ (x k - xb k) + D k *ᵥ (u k - ub k) + ly k)
    (k : ℕ) : -- --- CONCL ---
    y k = yb k + (C k * Conform.prodJac A k k) *ᵥ (x 0 - xb 0)
        + ∑ i ∈ Finset.range k, (C k * Conform.prodJac A k (k - i - 1) * B i) *ᵥ (u i - ub i)
        + D k *ᵥ (u k - ub k)
      + (C k *ᵥ ∑ j ∈ Finset.range k, Conform.prodJac A k (k - j - 1) *ᵥ lx j
        + ly k) := by -- --- PROOF ---
  rw [hy k, aux_dev_unroll x xb u ub A B lx hx k]
  simp only [mulVec_add, mulVec_sum, ← mulVec_mulVec, Finset.sum_add_distrib]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
