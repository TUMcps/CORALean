import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxWidthMulti
import CORALean.ContSet.PolyZonotope.Real.Cost.EDiff

/-!
# `PolyZonotope.relaxWidthMultiCost`

Asserted, not proved: `Operations/RelaxWidthMulti.lean` sums one `eDiff` per
factor, `p` of them and `p` additions.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxWidthMulti` costs at `p` factors. -/
def PolyZonotope.relaxWidthMultiCost (p : ℕ) : Cost := p • PolyZonotope.eDiffCost + ⟨p⟩

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxWidthMultiCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.relaxWidthMultiCost p ≤ PolyZonotope.relaxWidthMultiCost p' := by
  simp only [PolyZonotope.relaxWidthMultiCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul]
  have := Nat.mul_le_mul_right PolyZonotope.eDiffCost.ops h
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
