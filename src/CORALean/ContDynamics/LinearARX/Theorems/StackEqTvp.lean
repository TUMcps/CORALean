module

public import CORALean.ContDynamics.LinearARX.Theorems.BextEqZero
public import CORALean.ContDynamics.LinearARX.Theorems.BtildeSucc
public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTStep

@[expose] public section

/-!
# The window from the first outputs and the inputs alone

[1, Thm. 1]: on every ARMAX run, `ỹ(k:k₊) = Ã(k) ỹ_init + ∑_{i=0}^{k₊} B̃ᵢ(k) ũ(k₊ - i)` (7),
`k₊ = k + p - 1`, each input once. By induction on `k`: (11) is `toLinearSysDT_step`, and
`Btilde_succ` splits `B̃ᵢ(k+1)` into the new inputs, `feed`, and `Ā_ext` times the old sum.

## Inputs
* `sys` – ARX system
* `y` – outputs
* `u` – inputs
* `k` – step

## Hypotheses
* `hy` – the ARMAX recursion holds

## Conclusion
* the window is determined by the first window and the inputs

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". 2023 62nd IEEE Conference
      on Decision and Control (CDC), 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The lags `0..p` of (11), summed over a longer range, are `feed`. -/
private theorem LinearARX.aux_sum_Bext_eq_feed (sys : LinearARX 𝕋 dy du p) (u : ℕ → Vec ℝ du)
    (k : ℕ) : -- --- CONCL ---
    ∑ i ∈ Finset.range (k + p + 1), sys.Bext i *ᵥ u (k + p - i)
      = sys.feed u k := by -- --- PROOF ---
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : p + 1 ≤ k + p + 1))
    (fun i _ hi => by
      rw [sys.Bext_eq_zero (Or.inr (by rw [Finset.mem_range] at hi; omega)), zero_mulVec]),
    ← Fin.sum_univ_eq_sum_range (fun i => sys.Bext i *ᵥ u (k + p - i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.isLt
  unfold LinearARX.Bext
  rw [dif_pos (by omega)]
  congr 3

/-- No input is weighted at a negative index. -/
private theorem LinearARX.aux_Btilde_neg_one (sys : LinearARX 𝕋 dy du p) (k : ℕ) :
    sys.Btilde k (-1) = 0 := by
  unfold LinearARX.Btilde
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [sys.Bext_eq_zero (Or.inl (by omega)), Matrix.mul_zero]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.stack_eq_tvp (sys : LinearARX 𝕋 dy du p) {y : ℕ → Vec ℝ dy}
    {u : ℕ → Vec ℝ du}
    (hy : ∀ k, p ≤ k →
      y k = ∑ i : Fin p, toRealMat (sys.Abar i) *ᵥ y (k - (i + 1))
        + ∑ j : Fin (p + 1), toRealMat (sys.Bbar j) *ᵥ u (k - j)) (k : ℕ) : -- --- CONCL ---
    LinearARX.stack p y k = sys.Aext ^ k *ᵥ LinearARX.stack p y 0
      + ∑ i ∈ Finset.range (k + p), sys.Btilde k i *ᵥ u (k + p - 1 - i) := by -- --- PROOF ---
  induction k with
  | zero =>
    simp only [pow_zero, one_mulVec, zero_add, LinearARX.Btilde, Finset.range_zero,
      Finset.sum_empty, zero_mulVec, Finset.sum_const_zero, add_zero]
  | succ k ih =>
    rw [sys.toLinearSysDT_step hy k, ih, show toRealMat sys.toLinearSysDT.A = sys.Aext from rfl]
    -- split each new parameter into its new lag and `Ā_ext` times the old one
    have hsplit : ∀ i : ℕ, sys.Btilde (k + 1) i *ᵥ u (k + p + 1 - 1 - i)
        = sys.Bext i *ᵥ u (k + p - i) + sys.Aext *ᵥ (sys.Btilde k (i - 1) *ᵥ u (k + p - i)) := by
      intro i
      rw [sys.Btilde_succ, add_mulVec, mulVec_mulVec, show k + p + 1 - 1 - i = k + p - i by omega]
    rw [show k + 1 + p = k + p + 1 by omega, Finset.sum_congr rfl fun i _ => hsplit i,
      Finset.sum_add_distrib, sys.aux_sum_Bext_eq_feed, ← mulVec_sum, Finset.sum_range_succ',
      Nat.cast_zero, zero_sub, sys.aux_Btilde_neg_one, zero_mulVec, add_zero, mulVec_add,
      mulVec_mulVec, ← pow_succ']
    have hold : ∀ i ∈ Finset.range (k + p), sys.Btilde k (↑(i + 1) - 1) *ᵥ u (k + p - (i + 1))
        = sys.Btilde k i *ᵥ u (k + p - 1 - i) := by
      intro i _
      congr 2
      · push_cast; ring
      · omega
    rw [Finset.sum_congr rfl hold]
    abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
