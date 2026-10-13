import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpMulti
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxWidthMulti

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

/-- Monotone in the factor count. -/
theorem PolyZonotope.relaxExpMultiCost_mono {p p' : ℕ} (n : ℕ) (h : p ≤ p') :
    PolyZonotope.relaxExpMultiCost n p ≤ PolyZonotope.relaxExpMultiCost n p' :=
  Cost.add_le_add (le_refl _) (PolyZonotope.relaxWidthMultiCost_mono h)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
