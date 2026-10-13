import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxDrift
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.EDrift

/-!
# `PolyZonotope.relaxDriftCost`

Asserted, not proved: `Operations/RelaxDrift.lean` is written with `eDrift`
appearing four times, so four evaluations are counted, no sharing being
assumed; then two subtractions-or-additions and two halvings.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxDrift` costs at `p` factors. -/
def PolyZonotope.relaxDriftCost (p : ℕ) : Cost := (4 : ℕ) • PolyZonotope.eDriftCost p + ⟨4⟩

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxDriftCost_mono {p p' : ℕ} (h : p ≤ p') :
    PolyZonotope.relaxDriftCost p ≤ PolyZonotope.relaxDriftCost p' := by
  have := PolyZonotope.eDriftCost_mono h
  simp only [PolyZonotope.relaxDriftCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at this ⊢
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
