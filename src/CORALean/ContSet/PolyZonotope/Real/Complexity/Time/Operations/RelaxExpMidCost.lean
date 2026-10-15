module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMid
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxDriftCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpMidCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpMid.lean` evaluates
`relaxDrift` twice, once for the centre's shift (`n` products, `n` additions)
and once for the new generator's radius (`n` products), and adds the two named
generators (`n`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpMid` costs at `Vec ℝ n` and `p` factors. -/
def PolyZonotope.relaxExpMidCost (n p : ℕ) : Cost :=
  ⟨4 * n⟩ + (2 : ℕ) • PolyZonotope.relaxDriftCost p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
