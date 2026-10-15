module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthMultiCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpMultiCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpMulti.lean` adds the two
named generators (`n`), sums the widths over the `p` factors and scales the
first generator by the sum (`n`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpMulti` costs at `Vec ℝ n` and `p` factors. -/
def PolyZonotope.relaxExpMultiCost (n p : ℕ) : Cost :=
  ⟨2 * n⟩ + PolyZonotope.relaxWidthMultiCost p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
