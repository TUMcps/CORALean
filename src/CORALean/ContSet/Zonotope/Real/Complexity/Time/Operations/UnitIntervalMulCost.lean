module

public import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.unitIntervalMulCost`

Asserted, not proved: `Operations/UnitIntervalMul.lean` makes the old center the first generator
and the new center zero. Nothing is computed, but the result has a zero center of `n` entries and
`h + 1` generators of `n` entries each, `n * (h + 2)` scalars, each a write.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.unitIntervalMul` costs at `Vec ℝ n` on `h` generators: `n * (h + 2)` writes. -/
def Zonotope.unitIntervalMulCost (n h : ℕ) : Cost := ⟨n * (h + 2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
