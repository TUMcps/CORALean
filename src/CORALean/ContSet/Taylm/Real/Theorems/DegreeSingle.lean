import CORALean.ContSet.Taylm.Real.Operations.Degree

/-!
# A unit vector has degree one
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.degree_single (k : Fin n) : Taylm.degree (Pi.single k 1 : Fin n → ℕ) = 1 := by
  simp [Taylm.degree, Finset.sum_pi_single']

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
