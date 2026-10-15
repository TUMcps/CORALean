module

public import CORALean.ContSet.ConPolyZono.Real.Complexity.Time.Operations.MapCost
public import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

@[expose] public section

/-!
# `ConPolyZono.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` sends the center and each of the
`h + qI` generators through `M *ᵥ ·` and carries the constraint system over
unchanged, so the whole count is `mapCost` at `Cost.matVec k n`, the constraint system's entries
being writes of the result.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.mtimes` costs at `M : Mat ℝ k n` and `p` factors, `h`, `qI` generators, `m`
constraints over `q` constraint generators: one matrix-vector product for the center and one per
generator, and the writes of the carried blocks. -/
def ConPolyZono.mtimesCost (k n p h qI m q : ℕ) : Cost :=
  ConPolyZono.mapCost (Cost.matVec k n) p h qI m q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
