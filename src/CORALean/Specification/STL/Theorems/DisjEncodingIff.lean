module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The disjunction constraints compute the disjunction

[1, Sec. IV-B.2 (disjunction)]: for a continuous `z ∈ [0, 1]` and binary operands `z^{φᵢ}`, the
constraints `z ≥ z^{φᵢ}` and `z ≤ Σᵢ z^{φᵢ}` enforce `z = 1` if some operand holds and `z = 0`
otherwise: any feasible `z` is that value, and that value is feasible.

## Inputs
* `m` – number of operands
* `zs` – operand values

## Hypotheses
* `hzs` – every value is zero or one

## Conclusion
* the constraints force the disjunction and it exists

## References

* [1] [V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and S. A. Seshia.
      "Model Predictive Control with Signal Temporal Logic Specifications". 53rd IEEE Conference on
      Decision and Control, 2014.](../../../../../references/2014/raman-cdc-mpc-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.disj_encoding_iff {m : ℕ} (zs : Fin m → ℝ)
    (hzs : ∀ i, zs i = 0 ∨ zs i = 1) : -- --- CONCL ---
    (∀ z : ℝ, 0 ≤ z → z ≤ 1 → (∀ i, zs i ≤ z) → z ≤ ∑ i, zs i →
      (z = 0 ∨ z = 1) ∧ (z = 1 ↔ ∃ i, zs i = 1)) ∧
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧ (∀ i, zs i ≤ z) ∧ z ≤ ∑ i, zs i := by -- --- PROOF ---
  have hnn : ∀ i, 0 ≤ zs i := fun i => by rcases hzs i with h | h <;> simp [h]
  have hle : ∀ i, zs i ≤ 1 := fun i => by rcases hzs i with h | h <;> simp [h]
  -- with no operand `1` the sum is `0`; with one it is at least `1`
  have hnone : (∀ i, zs i ≠ 1) → ∑ i, zs i = 0 := fun h =>
    Finset.sum_eq_zero fun i _ => (hzs i).resolve_right (h i)
  have hone : ∀ j, zs j = 1 → 1 ≤ ∑ i, zs i := fun j hj =>
    hj ▸ Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ j)
  refine ⟨fun z hz0 hz1 hlo hhi => ?_, ?_⟩
  · by_cases h : ∃ i, zs i = 1
    · obtain ⟨j, hj⟩ := h
      have : z = 1 := by linarith [hlo j]
      exact ⟨Or.inr this, ⟨fun _ => ⟨j, hj⟩, fun _ => this⟩⟩
    · simp only [not_exists] at h
      have : z = 0 := by rw [hnone h] at hhi; linarith
      exact ⟨Or.inl this, ⟨fun h1 => absurd (this ▸ h1) (by norm_num),
        fun ⟨j, hj⟩ => absurd hj (h j)⟩⟩
  · by_cases h : ∃ i, zs i = 1
    · obtain ⟨j, hj⟩ := h
      exact ⟨1, by norm_num, le_rfl, hle, hone j hj⟩
    · simp only [not_exists] at h
      exact ⟨0, le_rfl, by norm_num, fun i => le_of_eq ((hzs i).resolve_right (h i)),
        by rw [hnone h]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
