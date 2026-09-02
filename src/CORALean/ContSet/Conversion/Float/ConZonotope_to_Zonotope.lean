import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
import CORALean.ContSet.Conversion.Real.ConZonotope_to_Zonotope

/-!
# Dropping the constraints, over a floating-point scalar

Forget what the coefficients had to satisfy and keep the generators. Nothing
rounds — the fields are copied, error box included — so the enclosure is the
exact layer's, carried across by `mono_subset`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def ConZonotope.zonotope (C : ConZonotope 𝕋 n) : Zonotope 𝕋 n := ⟨C.h, C.c, C.G, C.E⟩

variable [SoundFloatArithmetic 𝕋]

theorem ConZonotope.zonotope_outer (C : ConZonotope 𝕋 n) :
    C.construct ⊆ C.zonotope.construct :=
  mono_subset (Real.ConZonotope.zonotope_outer (nominal C)) subset_rfl

end CORALean.Float
