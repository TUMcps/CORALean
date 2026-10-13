import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope

/-!
# Dropping the constraints, over a floating-point scalar

Forget what the coefficients had to satisfy and keep the generators. Nothing
rounds — the fields are copied, error box included — so the enclosure is the
exact layer's, carried across by `mono_subset`.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ConZonotope.zonotope (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  ⟨cZ.h, cZ.c, cZ.G, cZ.E⟩

variable [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.zonotope_contains (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.zonotope.construct :=
  mono_subset (Real.ConZonotope.zonotope_contains (nominal cZ)) subset_rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
