module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The conjunction constraints compute the conjunction

[1, Sec. IV-B.2 (conjunction)]: for a continuous `z ∈ [0, 1]` and binary operands `z^{φᵢ}`, the
constraints `z ≤ z^{φᵢ}` and `z ≥ 1 - m + Σᵢ z^{φᵢ}` enforce `z = 1` if every operand holds and
`z = 0` otherwise. Both: any feasible `z` is that Boolean value, and that value is feasible.

## Inputs
* `m` – number of operands
* `zs` – operand values

## Hypotheses
* `hzs` – every value is zero or one

## Conclusion
* the constraints force the conjunction and it exists

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.conj_encoding_iff {m : ℕ} (zs : Fin m → ℝ) (hzs : ∀ i, zs i = 0 ∨ zs i = 1) :
    (∀ z : ℝ, 0 ≤ z → z ≤ 1 → (∀ i, z ≤ zs i) → 1 - m + ∑ i, zs i ≤ z →
      (z = 0 ∨ z = 1) ∧ (z = 1 ↔ ∀ i, zs i = 1)) ∧
    ∃ z : ℝ, 0 ≤ z ∧ z ≤ 1 ∧ (∀ i, z ≤ zs i) ∧ 1 - m + ∑ i, zs i ≤ z := by -- --- PROOF ---
  have hnn : ∀ i, 0 ≤ zs i := fun i => by rcases hzs i with h | h <;> simp [h]
  have hle : ∀ i, zs i ≤ 1 := fun i => by rcases hzs i with h | h <;> simp [h]
  -- with every operand `1` the sum is `m`; with one `0` it is at most `m - 1`
  have hall : (∀ i, zs i = 1) → ∑ i, zs i = m := fun h => by simp [h]
  have hsome : ∀ j, zs j = 0 → ∑ i, zs i ≤ m - 1 := fun j hj => by
    have hsplit := Finset.add_sum_erase Finset.univ zs (Finset.mem_univ j)
    have hrest : ∑ i ∈ Finset.univ.erase j, zs i ≤ ∑ i ∈ Finset.univ.erase j, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => hle i
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub (by have := j.2; omega)] at hrest
    push_cast at hrest
    linarith
  -- a feasible `z` is the Boolean value, and the Boolean value is feasible
  refine ⟨fun z hz0 hz1 hlo hhi => ?_, ?_⟩
  · by_cases h : ∀ i, zs i = 1
    · have : z = 1 := by rw [hall h] at hhi; linarith
      exact ⟨Or.inr this, ⟨fun _ => h, fun _ => this⟩⟩
    · simp only [not_forall] at h
      obtain ⟨j, hj⟩ := h
      have hj0 : zs j = 0 := (hzs j).resolve_right hj
      have : z = 0 := by linarith [hlo j]
      exact ⟨Or.inl this, ⟨fun h1 => absurd (this ▸ h1) (by norm_num), fun h1 => absurd (h1 j) hj⟩⟩
  · by_cases h : ∀ i, zs i = 1
    · exact ⟨1, by norm_num, le_rfl, fun i => by rw [h i], by rw [hall h]; linarith⟩
    · simp only [not_forall] at h
      obtain ⟨j, hj⟩ := h
      exact ⟨0, le_rfl, by norm_num, hnn, by linarith [hsome j ((hzs j).resolve_right hj)]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
