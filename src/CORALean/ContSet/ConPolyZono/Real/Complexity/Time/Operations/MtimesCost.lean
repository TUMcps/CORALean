module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConPolyZono.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the center and each of the
`h + qI` generators through `M *ᵥ ·` and carries the constraint system over
unchanged, so the whole count is `mapCost` at `Cost.matVec m n`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.mtimes` costs at `M : Mat ℝ k n` and `h`, `qI` generators:
one matrix-vector product for the center and one per generator. -/
def ConPolyZono.mtimesCost (k n h qI : ℕ) : Cost := ConPolyZono.mapCost (Cost.matVec k n) h qI

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
