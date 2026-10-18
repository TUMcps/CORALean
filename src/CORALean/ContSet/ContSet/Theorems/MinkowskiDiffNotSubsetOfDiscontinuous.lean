module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The fixed-point inclusion needs a continuous error

[1, Remark 1]: [1, Lemma 1]'s `A ⊖ B ⊆ S - 2c`, `S = {a + φ(a) | a ∈ A}`, fails once `φ`
may jump. With `A = B = [-1, 1]` (so `c = 0`), `A ⊖ B = {0}`, and `φ = sign` (`sign 0 = 1`)
maps `A` into `B` but gives `S = [-2, -1) ∪ [1, 2]`, which misses `0`. Lemma 1 itself, for a
continuous `φ`, is `minkowskiDiff_subset_of_continuous`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem minkowskiDiff_not_subset_of_discontinuous : -- --- STMT ---
    let φ : ℝ → ℝ := fun a => if 0 ≤ a then 1 else -1
    minkowskiDiff (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1) 1) = {0} ∧
      Set.MapsTo φ (Set.Icc (-1) 1) (Set.Icc (-1) 1) ∧
      {x | ∃ a ∈ Set.Icc (-1 : ℝ) 1, x = a + φ a} = Set.Ico (-2) (-1) ∪ Set.Icc 1 2 ∧
      ¬ minkowskiDiff (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1) 1)
        ⊆ {x | ∃ a ∈ Set.Icc (-1 : ℝ) 1, x = a + φ a} := by -- --- PROOF ---
  intro φ
  -- `A ⊖ B = {0}`: the shifts by `±1` pin `x` down
  have hdiff : minkowskiDiff (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1) 1) = {0} := by
    ext x
    simp only [minkowskiDiff, Set.mem_setOf_eq, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · intro h
      have h1 := h 1 ⟨by norm_num, le_rfl⟩
      have h2 := h (-1) ⟨le_rfl, by norm_num⟩
      linarith [h1.2, h2.1]
    · rintro rfl y hy
      constructor <;> linarith [hy.1, hy.2]
  -- `S`: the left half shifted down by one, the right half up by one
  have hS : {x | ∃ a ∈ Set.Icc (-1 : ℝ) 1, x = a + φ a} = Set.Ico (-2) (-1) ∪ Set.Icc 1 2 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_union, Set.mem_Ico, φ]
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      split_ifs with h
      · right; constructor <;> linarith
      · left; constructor <;> linarith [not_le.mp h]
    -- each half back to its preimage under `a ↦ a + φ(a)`
    · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
      · refine ⟨x + 1, ⟨by linarith, by linarith⟩, ?_⟩
        rw [if_neg (by linarith)]
        ring
      · refine ⟨x - 1, ⟨by linarith, by linarith⟩, ?_⟩
        rw [if_pos (by linarith)]
        ring
  refine ⟨hdiff, fun a _ => ?_, hS, fun h => ?_⟩
  · simp only [φ, Set.mem_Icc]
    split_ifs <;> norm_num
  · have h0 := h (hdiff ▸ Set.mem_singleton 0)
    rw [hS] at h0
    rcases h0 with ⟨-, h0⟩ | ⟨h0, -⟩ <;> norm_num at h0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
