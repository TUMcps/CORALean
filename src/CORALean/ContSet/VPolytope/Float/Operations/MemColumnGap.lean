import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap

/-!
# `columnGap` admits every column's rounding residual

Storing the lower rounding of one column leaves a residual the gap admits,
stated per column because that is how a vertex is placed.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Storing the lower rounding of column `l` leaves a residual the gap admits. -/
theorem VPolytope.mem_columnGap [SoundFloatArithmetic 𝕋] {k : ℕ} {lo hi : Mat 𝕋 n k}
    {p : Vec ℝ n} {l : Fin k}
    (h : ∀ i, toReal (lo i l) ≤ p i ∧ p i ≤ toReal (hi i l)) :
    (fun i => p i - toReal (lo i l)) ∈ (VPolytope.columnGap lo hi).construct := by
  refine fun i => ⟨?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ p i - toReal (lo i l)
    rw [toReal_zero]
    linarith [(h i).1]
  -- the column's own gap first, then the maximum over all of them
  · show p i - toReal (lo i l) ≤ toReal (maximumOver fun l' => subUp (hi i l') (lo i l'))
    calc p i - toReal (lo i l)
        ≤ toReal (hi i l) - toReal (lo i l) := by linarith [(h i).2]
      _ ≤ toReal (subUp (hi i l) (lo i l)) := sub_le_subUp _ _
      _ ≤ toReal (maximumOver fun l' => subUp (hi i l') (lo i l')) :=
          le_maximumOver (fun l' => subUp (hi i l') (lo i l')) l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
