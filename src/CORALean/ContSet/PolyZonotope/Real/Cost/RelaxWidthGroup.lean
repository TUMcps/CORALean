import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthGroup
import CORALean.ContSet.PolyZonotope.Real.Cost.EDiff

/-!
# `PolyZonotope.relaxWidthGroupCost`

Asserted, not proved: `Operations/RelaxWidthGroup.lean` is the same sum as
`relaxWidthMulti`, `p` `eDiff`s and `p` additions, for one grouped generator.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidthGroup` costs at `p` factors. -/
def PolyZonotope.relaxWidthGroupCost (p : ℕ) : Cost := p • PolyZonotope.eDiffCost + ⟨p⟩

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxWidthGroupCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.relaxWidthGroupCost p ≤ PolyZonotope.relaxWidthGroupCost p' := by
  simp only [PolyZonotope.relaxWidthGroupCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  have := Nat.mul_le_mul_right PolyZonotope.eDiffCost.ops h
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
