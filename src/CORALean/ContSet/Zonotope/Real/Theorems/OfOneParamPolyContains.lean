import CORALean.ContSet.Zonotope.Real.Operations.OfOneParamPoly
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# `Zonotope.ofOneParamPoly` holds its polynomial

For every `β ∈ [-1, 1]`, `Σ_{k=0}^N βᵏ v_k` is a point of the zonotope: generator `j` takes the
coefficient `β^{j+1}` when `j + 1` is odd and `2β^{j+1} - 1` when it is even, both in `[-1, 1]`,
and `βᵏ v_k = (2βᵏ - 1)(½ v_k) + ½ v_k` puts the rest of an even power in the centre. This is the
step of the proof of [1, Thm. 1] that turns the Taylor polynomial into a matrix zonotope.

## References

* [1] M. Althoff and J. M. Dolan. "Reachability Computation of Low-Order Models for the Safety
      Verification of High-Order Road Vehicle Models". In Proc. of the American Control
      Conference, pp. 3559-3566, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- The even powers among `1, …, N` are `2l` for `l = 1, …, ⌊N/2⌋`. -/
theorem aux_sum_range_even (f : ℕ → α) (N : ℕ) :
    ∑ k ∈ Finset.range N, (if Even (k + 1) then f (k + 1) else 0) =
      ∑ l ∈ Finset.Icc 1 (N / 2), f (2 * l) := by -- --- PROOF ---
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even (N + 1)
    · -- one more even power, `N + 1 = 2 ⌊(N+1)/2⌋`
      obtain ⟨t, ht⟩ := h
      have hdiv : (N + 1) / 2 = N / 2 + 1 := by omega
      rw [if_pos ⟨t, ht⟩, hdiv, Finset.sum_Icc_succ_top (by omega),
        show 2 * (N / 2 + 1) = N + 1 by omega]
    · -- none: the floor does not move
      rw [if_neg h, add_zero, show (N + 1) / 2 = N / 2 by
        rcases Nat.even_or_odd N with ⟨t, ht⟩ | ⟨t, ht⟩
        · omega
        · exact absurd ⟨t + 1, by omega⟩ h]

/-- One power: `βᵏ v = (coefficient) • (generator) + (its share of the centre)`. -/
theorem aux_pow_smul_split (v : α) (β : ℝ) (k : ℕ) :
    β ^ k • v = (if Odd k then β ^ k else 2 * β ^ k - 1) •
        (if Odd k then v else (1 / 2 : ℝ) • v) +
      (if Even k then (1 / 2 : ℝ) • v else 0) := by -- --- PROOF ---
  by_cases h : Odd k
  · rw [if_pos h, if_pos h, if_neg (Nat.not_even_iff_odd.2 h), add_zero]
  · rw [if_neg h, if_neg h, if_pos (Nat.not_odd_iff_even.1 h), smul_smul, ← add_smul]
    congr 1
    ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.ofOneParamPoly_contains (v : ℕ → α) (N : ℕ) {β : ℝ} (hβ : |β| ≤ 1) :
    ∑ k ∈ Finset.range (N + 1), β ^ k • v k ∈
      (Zonotope.ofOneParamPoly v N).construct := by -- --- PROOF ---
  refine ⟨fun j => if Odd (j.val + 1) then β ^ (j.val + 1) else 2 * β ^ (j.val + 1) - 1,
    fun j => ?_, ?_⟩
  · -- an odd power is in `[-1, 1]`, an even one in `[0, 1]`
    have h1 : |β ^ (j.val + 1)| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg β) hβ
    dsimp only
    by_cases h : Odd (j.val + 1)
    · rw [if_pos h]; exact h1
    · rw [if_neg h]
      have h0 : 0 ≤ β ^ (j.val + 1) := (Nat.not_odd_iff_even.1 h).pow_nonneg β
      rw [abs_of_nonneg h0] at h1
      rw [abs_le]; constructor <;> linarith
  · -- split every power into its generator's part and its centre's part
    show _ = v 0 + ∑ l ∈ Finset.Icc 1 (N / 2), (1 / 2 : ℝ) • v (2 * l) + ∑ j : Fin N,
      (if Odd (j.val + 1) then β ^ (j.val + 1) else 2 * β ^ (j.val + 1) - 1) •
        (if Odd (j.val + 1) then v (j.val + 1) else (1 / 2 : ℝ) • v (j.val + 1))
    rw [Fin.sum_univ_eq_sum_range (fun k => (if Odd (k + 1) then β ^ (k + 1)
      else 2 * β ^ (k + 1) - 1) • (if Odd (k + 1) then v (k + 1) else (1 / 2 : ℝ) • v (k + 1))) N,
      show ∑ l ∈ Finset.Icc 1 (N / 2), (1 / 2 : ℝ) • v (2 * l) = ∑ k ∈ Finset.range N,
        (if Even (k + 1) then (1 / 2 : ℝ) • v (k + 1) else 0) from
        (aux_sum_range_even (fun k => (1 / 2 : ℝ) • v k) N).symm, Finset.sum_range_succ', pow_zero,
      one_smul,
      Finset.sum_congr rfl fun k _ => aux_pow_smul_split (v (k + 1)) β (k + 1),
      Finset.sum_add_distrib]
    abel

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
