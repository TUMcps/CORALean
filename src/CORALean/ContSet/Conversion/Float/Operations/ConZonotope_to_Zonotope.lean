module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope

@[expose] public section

/-!
# Dropping the constraints, over a floating-point scalar — the construction

`ConZonotope.zonotope` is the construction; `ConZonotope_to_Zonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.zonotope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  ⟨cZ.h, cZ.c, cZ.G, cZ.I_error⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
