import CORALean.ContSet.LevelSet.Real.LevelSet

/-!
# Membership in a level set

The definition, unfolded: a point is in a level set exactly when every component meets its operator.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.mem_construct_iff (L : LevelSet n) (x : Vec ℝ n) :
    x ∈ L.construct ↔ ∀ i, (L.op i).holds (L.f x i) := Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
