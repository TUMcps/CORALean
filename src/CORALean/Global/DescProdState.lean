module

public import CORALean.Global.DescProd
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# A recursion `Δ(k+1) = A_k Δ(k) + B_k δ(k) + L_k` in closed form

The deviation `Δ` of a run from a reference obeys `Δ(k+1) = A_k Δ(k) + B_k δ(k) + L_k` when `L_k`
is what the linearization `A_k, B_k` leaves out. Unrolled, `Δ(k+1)` is the descending product
`A_k ... A_0` of `Δ(0)`, plus, for each `j ≤ k`, `A_k ... A_{j+1}` applied to `B_j δ(j)` and to
`L_j`: the `A{k}`, `B{k,j}` and `F{k,j}` of CORA's `computeGO_k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem descProd_state (A : ℕ → Mat ℝ n n) (B : ℕ → Mat ℝ n m) (Δ : ℕ → Vec ℝ n)
    (δ : ℕ → Vec ℝ m) (L : ℕ → Vec ℝ n)
    (h : ∀ k, Δ (k + 1) = A k *ᵥ Δ k + B k *ᵥ δ k + L k) (k : ℕ) : -- --- CONCL ---
    Δ (k + 1) = descProd A k (k + 1) *ᵥ Δ 0
      + ∑ j ∈ Finset.range (k + 1), (descProd A k (k - j) * B j) *ᵥ δ j
      + ∑ j ∈ Finset.range (k + 1), descProd A k (k - j) *ᵥ L j := by -- --- PROOF ---
  induction k with
  | zero =>
    -- one step: the products are `A 0` and the empty product
    simp [h 0, descProd]
  | succ k ih =>
    -- the next step multiplies every term of the previous one by `A (k+1)`
    have hp : ∀ j ∈ Finset.range (k + 1),
        descProd A (k + 1) (k + 1 - j) = A (k + 1) * descProd A k (k - j) := fun j hj => by
      have : k + 1 - j = (k - j) + 1 := by have := Finset.mem_range.1 hj; omega
      rw [this]; simp [descProd]
    -- the two sums over `range (k+2)`: the last term, and `A (k+1)` times the rest
    have hB : ∑ j ∈ Finset.range (k + 2), (descProd A (k + 1) (k + 1 - j) * B j) *ᵥ δ j
        = A (k + 1) *ᵥ ∑ j ∈ Finset.range (k + 1), (descProd A k (k - j) * B j) *ᵥ δ j
          + B (k + 1) *ᵥ δ (k + 1) := by
      rw [Finset.sum_range_succ, Matrix.mulVec_sum]
      simp only [Nat.sub_self, descProd, Matrix.one_mul, Matrix.mulVec_mulVec]
      rw [Finset.sum_congr rfl fun j hj => by rw [hp j hj, Matrix.mul_assoc]]
    have hL : ∑ j ∈ Finset.range (k + 2), descProd A (k + 1) (k + 1 - j) *ᵥ L j
        = A (k + 1) *ᵥ ∑ j ∈ Finset.range (k + 1), descProd A k (k - j) *ᵥ L j
          + L (k + 1) := by
      rw [Finset.sum_range_succ, Matrix.mulVec_sum]
      simp only [Nat.sub_self, descProd, Matrix.one_mulVec, Matrix.mulVec_mulVec]
      rw [Finset.sum_congr rfl fun j hj => by rw [hp j hj]]
    have h0 : descProd A (k + 1) (k + 2) = A (k + 1) * descProd A k (k + 1) := by
      simp [descProd]
    rw [h (k + 1), ih, hB, hL, h0]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
