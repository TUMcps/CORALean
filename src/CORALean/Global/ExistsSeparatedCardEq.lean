module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# `W` times `M + 1` apart, away from `d` given ones

The count of [1, Thm. 4]: among the times `0, …, N - 1`, given `d` of them `H`, there are
`W = ⌈(N - d(2M + 1))/(M + 1)⌉` times more than `M` apart from each other and from every time of
`H`. Removing the `M`-neighbourhoods of `H`, at most `d(2M + 1)` times, leaves at least
`N - d(2M + 1)`; some residue class modulo `M + 1` holds at least a `1/(M + 1)` share of them
(pigeonhole), and two times of one class are at least `M + 1` apart.

## Inputs
* `N` – number of times
* `M` – separation
* `H` – given times

## Hypotheses
* none

## Conclusion
* a set of the stated size exists whose times are separated from each other and from the given ones

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- two times of one residue class modulo `M + 1` are more than `M` apart
theorem aux_sep_of_mod_eq {a b M : ℕ} (hab : a < b) (h : a % (M + 1) = b % (M + 1)) :
    a + M < b := by
  have hd : (M + 1) ∣ b - a := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  have := Nat.le_of_dvd (by omega) hd
  omega


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_separated_card_eq (N M : ℕ) (H : Finset (Fin N)) :
    ∃ J : Finset (Fin N), J.card = ⌈((N : ℝ) - H.card * (2 * M + 1)) / (M + 1)⌉₊ ∧
      ∀ j ∈ J, (∀ h ∈ H, h.val + M < j.val ∨ j.val + M < h.val) ∧
        ∀ j' ∈ J, j' ≠ j → j'.val + M < j.val ∨ j.val + M < j'.val := by -- --- PROOF ---
  classical
  set W := ⌈((N : ℝ) - H.card * (2 * M + 1)) / (M + 1)⌉₊ with hW
  -- the `M`-neighbourhoods of `H`, and the times left
  let D := H.biUnion fun h => Finset.univ.filter fun t : Fin N => h.val ≤ t.val + M ∧
    t.val ≤ h.val + M
  let R := Finset.univ \ D
  have hDc : D.card ≤ H.card * (2 * M + 1) := by
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_).trans
      (by rw [smul_eq_mul]))
    refine (Finset.card_le_card_of_injOn (fun t : Fin N => t.val) (t := Finset.Icc (h.val - M)
      (h.val + M)) (fun t ht => ?_) Fin.val_injective.injOn).trans ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
      simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    · rw [Nat.card_Icc]; omega
  have hRc : N ≤ R.card + H.card * (2 * M + 1) := by
    have : R.card = N - D.card := by
      simp only [R, Finset.card_univ_sdiff, Fintype.card_fin]
    omega
  rcases Nat.eq_zero_or_pos W with hW0 | hWpos
  · exact ⟨∅, by simp [hW0], by simp⟩
  -- some residue class holds `W` of the times left
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hlt : (M + 1) * (W - 1) < R.card := by
    have h1 : ((W - 1 : ℕ) : ℝ) < ((N : ℝ) - H.card * (2 * M + 1)) / (M + 1) :=
      Nat.lt_ceil.mp (by omega)
    rw [lt_div_iff₀ hM1] at h1
    have h2 : (N : ℝ) ≤ R.card + H.card * (2 * M + 1) := by exact_mod_cast hRc
    have h3 : ((W - 1 : ℕ) : ℝ) * (M + 1) < R.card := by linarith
    have h4 : (((M + 1) * (W - 1) : ℕ) : ℝ) < R.card := by push_cast; linarith
    exact_mod_cast h4
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := fun t : Fin N => t.val % (M + 1)) (t := Finset.range (M + 1))
    (fun t _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega))) (by rwa [Finset.card_range])
  obtain ⟨J, hJF, hJc⟩ := Finset.exists_subset_card_eq (show W ≤ (R.filter fun t =>
    t.val % (M + 1) = c).card by omega)
  refine ⟨J, hJc, fun j hj => ⟨fun h hh => ?_, fun j' hj' hne => ?_⟩⟩
  · -- outside the neighbourhood of `h`
    have hjR := (Finset.mem_filter.mp (hJF hj)).1
    have hjD : j ∉ D := (Finset.mem_sdiff.mp hjR).2
    have : ¬ (h.val ≤ j.val + M ∧ j.val ≤ h.val + M) := fun hw =>
      hjD (Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩)
    omega
  · -- one residue class
    have h1 := (Finset.mem_filter.mp (hJF hj)).2
    have h2 := (Finset.mem_filter.mp (hJF hj')).2
    have hv : j'.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hv with h | h
    · exact Or.inl (aux_sep_of_mod_eq h (h2.trans h1.symm))
    · exact Or.inr (aux_sep_of_mod_eq h (h1.trans h2.symm))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
