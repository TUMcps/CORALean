module

public import CORALean.ContSet.LevelSet.Real.Operations.Plus

@[expose] public section

/-!
# `LevelSet.plus` is exact

The image under a translation is the level set of the substituted function, with equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LevelSet.plus_exact (L : LevelSet n) (v : Vec ℝ n) :
    (L.plus v).construct = (· + v) '' L.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro h
    exact ⟨y - v, h, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    intro i
    simpa [LevelSet.plus] using hx i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
