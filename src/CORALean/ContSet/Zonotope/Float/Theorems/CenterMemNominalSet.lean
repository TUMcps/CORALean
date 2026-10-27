module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.CenterMemConstruct

@[expose] public section

/-!
# The stored center is a point of the nominal zonotope

CORA's `center` of a matrix zonotope is its stored center `C`, which takes no arithmetic. Read as
reals, it lies in the exact zonotope the stored floats describe, at the zero coefficients. It lies
in the set the float zonotope denotes, the nominal part plus the error box, only when that box
holds `0`, which a stored box need not.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the stored center, read as reals, lies in the nominal zonotope
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [Entrywise β ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.center_mem_nominalSet (Z : Zonotope α) :
    RealImage.realImage Z.c ∈ InflatedContSet.nominalSet Z :=
  Real.Zonotope.center_mem_construct (InflatedContSet.nominal Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
