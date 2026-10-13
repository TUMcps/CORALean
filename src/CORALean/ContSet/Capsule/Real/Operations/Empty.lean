module

public import CORALean.ContSet.Capsule.Real.Capsule

@[expose] public section

/-!
# `Capsule.empty`

CORA's `capsule.empty(n)`, a capsule with no generator and no radius. The model has no
zero-width capsule, so the empty one is the one with radius `-1`, as `Capsule`'s own docstring
says.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `capsule.empty(n)`: radius `-1`, which no point is within. -/
def Capsule.empty (n : ℕ) : Capsule n := ⟨0, 0, -1⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
