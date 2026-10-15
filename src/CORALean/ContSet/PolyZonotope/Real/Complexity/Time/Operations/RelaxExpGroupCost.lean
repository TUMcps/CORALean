module

public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxWidthGroupCost

@[expose] public section

/-!
# `PolyZonotope.relaxExpGroupCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpGroup.lean` merges `k`
generators into one of `d` kept ones. Summing the `k` merged generators is
`n * k` additions and adding that to the target `n`; the `d` kept generators
are each compared against the target index; and each of the `k` merged
generators gets its width over `p` factors and a scaling (`n`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpGroup` costs at `Vec ℝ n`, `p` factors, `d` kept
and `k` merged generators. -/
def PolyZonotope.relaxExpGroupCost (n p d k : ℕ) : Cost :=
  ⟨n * (k + 1) + d + k * n⟩ + k • PolyZonotope.relaxWidthGroupCost p

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
