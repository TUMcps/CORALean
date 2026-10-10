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
theorem VPolytope.mem_columnGap [SoundFloatArithmetic 𝕋] {k : ℕ} {lo hi : Fin k → Vec 𝕋 n}
    {p : Vec ℝ n} {l : Fin k}
    (h : ∀ i, toReal (lo l i) ≤ p i ∧ p i ≤ toReal (hi l i)) :
    (fun i => p i - toReal (lo l i)) ∈ (VPolytope.columnGap lo hi).construct := by -- --- PROOF ---
  refine fun i => ⟨?_, ?_⟩
  · show toReal (zero : 𝕋) ≤ p i - toReal (lo l i)
    rw [toReal_zero]
    linarith [(h i).1]
  -- the column's own gap first, then the maximum over all of them
  · show p i - toReal (lo l i) ≤ toReal (maximumOver fun l' => subUp (hi l' i) (lo l' i))
    calc p i - toReal (lo l i)
        ≤ toReal (hi l i) - toReal (lo l i) := by linarith [(h i).2]
      _ ≤ toReal (subUp (hi l i) (lo l i)) := sub_le_subUp _ _
      _ ≤ toReal (maximumOver fun l' => subUp (hi l' i) (lo l' i)) :=
          le_maximumOver (fun l' => subUp (hi l' i) (lo l' i)) l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
