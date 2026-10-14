module

public import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingCell
public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound

@[expose] public section

/-!
# `LevelSet.isIntersecting_` in the cell branch, without `==`

As `isIntersecting_uniform_outer`, for a cell of operators none of which is `==`: a negative
verdict proves the level set misses the box. The `==` rows are unsound
(`IsIntersectingCellCounterexample`). Outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.isIntersecting_cell_outer (L : LevelSet n) (hne : ∀ i, L.op i ≠ .eq)
    (I : Interval (Vec ℝ n)) (B : Fin L.m → Interval ℝ) {tol : ℝ} (htol : 0 ≤ tol)
    (hB : ∀ i, IsRangeBound (fun x => L.f x i) I.construct (B i).inf (B i).sup)
    (h : ¬ LevelSet.isIntersecting_cell tol L.op B) :
    L.construct ∩ I.construct = ∅ := by -- --- PROOF ---
  classical
  -- some row fails the test; a common point would satisfy it
  simp only [LevelSet.isIntersecting_cell, not_forall] at h
  obtain ⟨i, hi⟩ := h
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hxL hxI
  have h1 := hxL i
  have h2 := hB i x hxI
  apply hi
  rcases hop : L.op i with _ | _ | _
  · -- le: `f x i ≤ 0` forces `lb ≤ 0`
    rw [hop] at h1
    simp only [CompOp.holds] at h1
    dsimp only
    rcases lt_or_eq_of_le (h2.1.trans h1) with h | h
    · exact Or.inl h
    · right
      rw [h, abs_zero]; exact htol
  · -- lt: `f x i < 0` forces `lb < 0`
    rw [hop] at h1
    simp only [CompOp.holds] at h1
    dsimp only
    exact lt_of_le_of_lt h2.1 h1
  · exact absurd hop (hne i)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
