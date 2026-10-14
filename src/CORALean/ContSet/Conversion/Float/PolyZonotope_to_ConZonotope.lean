module

public import CORALean.ContSet.Conversion.Float.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.ConZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.PolyZonotope_to_ConZonotope

@[expose] public section

/-!
# A polynomial zonotope as a zonotope, and a constrained one as a constrained
zonotope, over a floating-point scalar

Every dependent factor's monomial lies in `[-1,1]`, so it is read as a free factor
of a zonotope, the dependent generators and then the independent ones; the error
box is carried across. Nothing rounds, and the exponents are dropped, which is
what makes this an enclosure rather than the set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.conZonotope_contains (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.conZonotope.construct :=
  subset_trans pZ.zonotope_contains pZ.zonotope.conZonotope_contains

theorem ConPolyZono.conZonotope_contains (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.conZonotope.construct :=
  subset_trans cPZ.polyZonotope_contains cPZ.polyZonotope.conZonotope_contains

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
