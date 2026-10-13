module

public import CORALean.ContSet.LevelSet.Float.Operations.IsIntersectingCell
public import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingCellOuter

@[expose] public section

/-!
# A `false` from `LevelSet.isIntersecting_cell` proves disjointness

For a level set without `=` rows, as the real theorem
`CORALean.Real.LevelSet.isIntersecting_cell_outer` needs: the refuting row's certified
comparison makes the real test fail at the bounds read as reals. A `true` says nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.isIntersecting_cell_outer (L : CORALean.Real.LevelSet n)
    (hne : ∀ i, L.op i ≠ .eq) (I : Interval (Vec 𝕋 n)) (B : Fin L.m → 𝕋 × 𝕋) {tol : 𝕋}
    (htol : 0 ≤ toReal tol)
    (hB : ∀ i, CORALean.Real.IsRangeBound (fun x => L.f x i) I.construct
      (toReal (B i).1) (toReal (B i).2))
    (h : LevelSet.isIntersecting_cell tol L.op B = false) :
    L.construct ∩ I.construct = ∅ := by -- --- PROOF ---
  refine CORALean.Real.LevelSet.isIntersecting_cell_outer L hne I.nominal
    (fun i => (toReal (B i).1, toReal (B i).2)) htol hB ?_
  -- the refuting row, and the real test failing there
  simp only [LevelSet.isIntersecting_cell, List.all_eq_false, List.mem_finRange, true_and,
    Bool.not_eq_true', Bool.not_eq_false] at h
  obtain ⟨i, hi⟩ := h
  intro hall
  have hr := hall i
  rcases hop : L.op i with _ | _ | _
  · -- le: `tol < lb`
    rw [hop] at hi hr
    have hlt := toReal_lt_of_ltStrict hi
    rcases hr with hr | hr
    · exact absurd hr (by simp only; linarith)
    · have := (abs_le.mp hr).2
      simp only at this
      linarith
  · -- lt: `0 ≤ lb`
    rw [hop] at hi hr
    have hle := toReal_le_of_le hi
    rw [toReal_zero] at hle
    exact absurd hr (by simp only; linarith)
  · exact absurd hop (hne i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
