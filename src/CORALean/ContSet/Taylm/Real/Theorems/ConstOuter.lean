import CORALean.ContSet.Taylm.Real.Operations.Const

/-!
# `Taylm.const` encloses the constant
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.const_outer (c : ℝ) (N : ℕ) : (Taylm.const n c N).Encloses fun _ => c := by
  intro t _
  simp [Taylm.const, Taylm.poly, Taylm.monomial_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
