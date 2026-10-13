import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.ofCenterRadius`

CORA's constructor `intervalMatrix(C, Δ)` from a centre and a half-width: the box `[C - Δ, C + Δ]`.
`Interval (Mat ℝ m n)` is already the interval matrix, so this is the same representation under
another description, and `Theorems/MemOfCenterRadius` reads it back.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.ofCenterRadius (c r : α) : Interval α := ⟨c - r, c + r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
