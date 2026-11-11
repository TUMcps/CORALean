module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# The nominal point of a polynomial zonotope, written out

The point `pZ.nominal.point a` of the exact polynomial zonotope the stored floats describe is the
center plus the generators times their monomials at the factor values `a`: the sum
the points of a fiber (`fiber`) are written with.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the nominal point is the center plus the weighted generators
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The nominal point, written with the stored floats read as reals. -/
theorem PolyZonotope.nominal_point_eq (pZ : PolyZonotope (Vec 𝕋 n)) (a : Fin pZ.p → ℝ) :
    pZ.nominal.point a = fun i => toReal (pZ.c i)
      + ∑ l, toReal (pZ.G l i) * Real.PolyZonotope.monomial pZ.E a l := by
  funext i
  simp only [Real.PolyZonotope.point, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [RealImage.realImage, mul_comm]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
