module

public import CORALean.ContSet.Capsule.Real.Operations.EnclosePoints
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Capsule.enclosePointsCost`

Asserted, not proved: `Operations/EnclosePoints.lean` at `N` points of
`Vec ℝ n`: the mean is `N * n` additions and `n` scalings, and then per point
the deviation `d` (`n`), its squared length for the `argmax` (`2 * n` and one
comparison), the rejection from the farthest direction (two dot products,
`4 * n`, one division, `n` products and `n` subtractions) and its norm
(`2 * n` and a `sqrt`) with one `max`: `11 * n + 4` per point.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Capsule.enclosePoints` costs for `N` points of `Vec ℝ n`. -/
def Capsule.enclosePointsCost (n N : ℕ) : Cost := ⟨N * (12 * n + 4) + n⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
