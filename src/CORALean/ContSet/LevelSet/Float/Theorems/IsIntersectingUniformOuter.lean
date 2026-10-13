module

public import CORALean.ContSet.LevelSet.Float.Operations.IsIntersectingUniform
public import CORALean.ContSet.LevelSet.Real.Theorems.IsIntersectingUniformOuter

@[expose] public section

/-!
# A `false` from `LevelSet.isIntersecting_uniform` proves disjointness

The refuting row's certified comparison, read as reals by `toReal_le_of_le` and
`toReal_lt_of_ltStrict`, makes the real test fail at the bounds read as reals, and the real
theorem `CORALean.Real.LevelSet.isIntersecting_uniform_outer` does the rest at the box the float
interval denotes. A `true` says nothing, as over ℝ.
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

theorem LevelSet.isIntersecting_uniform_outer (L : CORALean.Real.LevelSet n)
    (op : CORALean.Real.CompOp) (hop : ∀ i, L.op i = op) (I : Interval (Vec 𝕋 n))
    (B : Fin L.m → 𝕋 × 𝕋) {tol : 𝕋} (htol : 0 ≤ toReal tol)
    (hB : ∀ i, CORALean.Real.IsRangeBound (fun x => L.f x i) I.construct
      (toReal (B i).1) (toReal (B i).2))
    (h : LevelSet.isIntersecting_uniform tol op B = false) :
    L.construct ∩ I.construct = ∅ := by -- --- PROOF ---
  refine CORALean.Real.LevelSet.isIntersecting_uniform_outer L op hop I.nominal
    (fun i => (toReal (B i).1, toReal (B i).2)) htol hB ?_
  -- the refuting row, and the real test failing there
  simp only [LevelSet.isIntersecting_uniform, List.all_eq_false, List.mem_finRange, true_and,
    Bool.not_eq_true', Bool.not_eq_false] at h
  obtain ⟨i, hi⟩ := h
  intro hall
  have hr := hall i
  cases op with
  | eq =>
    -- `=`: either `tol < lb` or `ub < -tol` is certified
    simp only [Bool.or_eq_true] at hi
    obtain ⟨hu, hl⟩ := hr
    rcases hi with hi | hi
    · have hlt := toReal_lt_of_ltStrict hi
      rcases hl with hl | hl
      · exact absurd hl (by simp only; linarith)
      · have := (abs_le.mp hl).2
        simp only at this
        linarith
    · have hlt := toReal_lt_of_ltStrict hi
      rw [toReal_neg] at hlt
      rcases hu with hu | hu
      · exact absurd hu (by simp only; linarith)
      · have := (abs_le.mp hu).1
        simp only at this
        linarith
  | le =>
    -- `≤`: `tol < lb` is certified
    have hlt := toReal_lt_of_ltStrict hi
    rcases hr with hr | hr
    · exact absurd hr (by simp only; linarith)
    · have := (abs_le.mp hr).2
      simp only at this
      linarith
  | lt =>
    -- `<`: `0 ≤ lb` is certified
    have hle := toReal_le_of_le hi
    rw [toReal_zero] at hle
    exact absurd hr (by simp only; linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
