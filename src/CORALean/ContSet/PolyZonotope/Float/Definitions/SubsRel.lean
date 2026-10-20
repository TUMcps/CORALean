module

public import CORALean.ContSet.PolyZonotope.Float.Operations.SubsMul
public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsMul
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi
public import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners

@[expose] public section

/-!
# A term list brackets an exact one

The float terms `subsMul`, `subsPow`, `subsXprod` and `subsTerms` build carry a bracket for each
coefficient, not the exact real one the exact layer's lists carry. `subsRel A A'` says the lists
have the same length, the same exponents, and each coefficient of `A'` is between the floats of
the matching term of `A`.

## Inputs
* `A` – float term list (interval coefficients)
* `A'` – real term list

## Output
* relation: equal exponents, real coefficients inside the float intervals
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `subsRel A A'` says the float term list `A` encloses the real term list `A'` term by term:
the lists have the same length, and matching terms have the same exponent vector and the real
coefficient lies inside the float interval (between its `inf` and `sup`). -/
def PolyZonotope.subsRel (A : List ((Interval 𝕋) × (Fin p → ℕ))) (A' : List (ℝ × (Fin p →
    ℕ))) : Prop :=
  List.Forall₂ (fun s t => s.2 = t.2 ∧ toReal s.1.inf ≤ t.1 ∧ t.1 ≤ toReal s.1.sup) A A'

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
