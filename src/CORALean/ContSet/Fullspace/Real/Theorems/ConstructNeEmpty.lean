import CORALean.ContSet.Fullspace.Real.Fullspace

/-!
# The full space is not empty

`representsa_(fs,'emptySet')` is `false` for `fullspace`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.construct_ne_empty (F : Fullspace n) : F.construct ≠ ∅ := by
  intro h
  have : (0 : Vec ℝ n) ∈ F.construct := Set.mem_univ _
  rw [h] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
