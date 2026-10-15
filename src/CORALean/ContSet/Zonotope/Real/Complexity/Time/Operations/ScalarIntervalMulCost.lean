module

public import CORALean.ContSet.Zonotope.Real.Operations.ScalarIntervalMul
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.UnitIntervalMulCost

@[expose] public section

/-!
# `Zonotope.scalarIntervalMulCost`

Asserted, not proved, by reading `Operations/ScalarIntervalMul.lean` as written:
the midpoint and half-width of `[a, b]` (two operations each), two
`Zonotope.mtimes` by a scalar multiple of the identity, applied as the dense
matrices they are, a `plus` and a `unitIntervalMul`. A caller who multiplies by
a scalar directly would pay less, which is not what this definition does.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.scalarIntervalMul` costs at `Vec ℝ n` and `h` generators. -/
def Zonotope.scalarIntervalMulCost (n h : ℕ) : Cost :=
  ⟨4⟩ + (2 : ℕ) • Zonotope.mtimesCost n n h + Zonotope.plusCost n + Zonotope.unitIntervalMulCost

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
