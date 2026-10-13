module

public import CORALean.ContSet.LevelSet.Real.Operations.IsIntersectingUniform
public import CORALean.ContSet.LevelSet.Real.Definitions.RangeBound

@[expose] public section

/-!
# `LevelSet.isIntersecting_` rules out an intersection

If the bounds `B i` are a range bound of row `i` of the function over the box `I`, a negative
verdict means the level set misses the box: `isIntersecting_ = false` is a proof of disjointness
(one operator for every row, `tol ≥ 0`). Outer only: a positive verdict says nothing, and no
exactness is claimed.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.isIntersecting_uniform_outer (L : LevelSet n) (op : CompOp)
    (hop : ∀ i, L.op i = op) (I : Interval (Vec ℝ n)) (B : Fin L.m → ℝ × ℝ) {tol : ℝ}
    (htol : 0 ≤ tol)
    (hB : ∀ i, IsRangeBound (fun x => L.f x i) I.construct (B i).1 (B i).2)
    (h : ¬ LevelSet.isIntersecting_uniform tol op B) :
    L.construct ∩ I.construct = ∅ := by -- --- PROOF ---
  classical
  -- some row fails the test; a common point would satisfy it
  simp only [LevelSet.isIntersecting_uniform, not_forall] at h
  obtain ⟨i, hi⟩ := h
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hxL hxI
  have h1 := hxL i
  rw [hop i] at h1
  have h2 := hB i x hxI
  apply hi
  cases op <;> simp only [CompOp.holds] at h1 ⊢
  · -- le: `f x i ≤ 0` forces `lb ≤ 0`
    rcases lt_or_eq_of_le (h2.1.trans h1) with h | h
    · exact Or.inl h
    · right
      rw [h, abs_zero]; exact htol
  · exact lt_of_le_of_lt h2.1 h1
  · -- eq: `f x i = 0` forces `lb ≤ 0 ≤ ub`
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le (h1 ▸ h2.2 : 0 ≤ (B i).2) with h | h
      · exact Or.inl h
      · right; rw [← h, abs_zero]; exact htol
    · rcases lt_or_eq_of_le (h1 ▸ h2.1 : (B i).1 ≤ 0) with h | h
      · exact Or.inl h
      · right; rw [h, abs_zero]; exact htol


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
