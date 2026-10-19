module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDiffTight

@[expose] public section

/-!
# `eDiffTight` is nonnegative

The generator the relaxation adds is `eDiffTight` times a generator, and the coefficient that the
difference asks of it (`Zonotope.coefficient`) is stated for a nonnegative width.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The maximum of an absolute value is nonnegative. -/
theorem PolyZonotope.eDiffTight_nonneg (a b : ℕ) : 0 ≤ PolyZonotope.eDiffTight a b := by
  unfold PolyZonotope.eDiffTight
  split_ifs <;> positivity

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
