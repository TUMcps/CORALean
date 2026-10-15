module

public import CORALean.ContSet.Taylm.Real.Operations.Mag

@[expose] public section

/-!
# The hull of a Taylor model lies within its magnitude
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.abs_le_mag (T : Taylm n) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (min T.constCoef T.bounds.inf) (max T.constCoef T.bounds.sup)) :
    |ξ| ≤ T.mag := by -- --- PROOF ---
  unfold Taylm.mag
  have h1 := le_max_left |T.constCoef| (max |T.bounds.inf| |T.bounds.sup|)
  have h2 := le_max_left |T.bounds.inf| |T.bounds.sup|
  have h3 := le_max_right |T.bounds.inf| |T.bounds.sup|
  have h4 := le_max_right |T.constCoef| (max |T.bounds.inf| |T.bounds.sup|)
  rw [abs_le]
  constructor
  · -- the lower end of the hull is the center or the range's bottom
    have := hξ.1
    rcases min_choice T.constCoef T.bounds.inf with h | h <;> rw [h] at this
    · linarith [neg_abs_le T.constCoef]
    · linarith [neg_abs_le T.bounds.inf]
  · have := hξ.2
    rcases max_choice T.constCoef T.bounds.sup with h | h <;> rw [h] at this
    · linarith [le_abs_self T.constCoef]
    · linarith [le_abs_self T.bounds.sup]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
