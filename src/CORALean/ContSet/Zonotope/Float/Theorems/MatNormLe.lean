module

public import CORALean.ContSet.Zonotope.Float.Operations.MatNorm
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeMatIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.MatNormLe

@[expose] public section

/-!
# `Zonotope.matNorm` bounds the norm of every member

Every member of the zonotope lies in its enclosing box (`matInterval_contains`), and
`Interval.matNorm_le` bounds the norm of the members of the box by the float norm.

## Inputs
* `steps` – number of Newton steps of the square root
* `p` – norm type
* `Z` – matrix zonotope
* `M` – member matrix

## Hypotheses
* `hM` – `M` lies in the zonotope

## Conclusion
* the norm of `M` is at most the float norm
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.matNorm_le (steps : ℕ) (p : Real.Interval.NormType) (Z : Zonotope (Mat 𝕋 m n))
    {M : Mat ℝ m n} (hM : M ∈ Z.construct) :
    p.eval M ≤ toReal (Z.matNorm steps p) :=
  Interval.matNorm_le steps p Z.matInterval (Zonotope.matInterval_contains Z hM)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
