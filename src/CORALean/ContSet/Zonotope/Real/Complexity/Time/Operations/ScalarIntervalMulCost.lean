module

public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.PlusCost
public import CORALean.ContSet.Zonotope.Real.Operations.ScalarIntervalMul
public import CORALean.ContSet.Zonotope.Real.Operations.UnitIntervalMul
public import CORALean.Global.Cost
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.scalarIntervalMulCost`

Asserted, not proved, by reading `Operations/ScalarIntervalMul.lean` as written:
the midpoint and half-width of `[a, b]` (two operations each), two
`Zonotope.mtimes` by a scalar multiple of the identity, applied as the dense
matrices they are, a `plus` and a `unitIntervalMul`. A caller who multiplies by
a scalar directly would pay less, which is not what this definition does.

Each scaled identity is a result of its own, `n * n` writes; the `plus` joins the product's `h`
generators to the `h + 1` of the unit-interval product.

## Inputs
* `n` – dimension
* `h` – generator count

## Output
* cost of the scalars, scaled identities, products and sum
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- What `Zonotope.unitIntervalMul` costs at `Vec ℝ n` on `h` generators: `n * (h + 2)` writes. -/
@[step_of Zonotope.scalarIntervalMulCost]
def Zonotope.step_unitIntervalMulCost (n h : ℕ) : Cost := ⟨n * (h + 2)⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.scalarIntervalMul` costs at `Vec ℝ n` and `h` generators: the two scalars,
the `n * n` writes of each scaled identity, the two products, the sum and the unit-interval
product. -/
def Zonotope.scalarIntervalMulCost (n h : ℕ) : Cost :=
  ⟨4 + 2 * (n * n)⟩ + (2 : ℕ) • Zonotope.mtimesCost n n h + Zonotope.plusCost n h (h + 1) +
    Zonotope.step_unitIntervalMulCost n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
