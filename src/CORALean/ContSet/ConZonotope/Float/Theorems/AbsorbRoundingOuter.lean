module

public import CORALean.ContSet.ConZonotope.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `ConZonotope.absorbRounding` loses no point

Read back through `ContSet`, for a caller that only wants the inclusion:
`absorbRounding_nominal` places every point in the nominal set, and the result's box denotes the
origin alone. The box of the result is exactly zero, so nothing of the absorption step's rounding
is left outside the nominal set.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `absorbRounding` contains the set. -/
theorem ConZonotope.absorbRounding_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.construct ⊆ cZ.absorbRounding.construct := fun x hx =>
  ⟨x, ConZonotope.absorbRounding_nominal cZ hx, 0,
    fun i => ⟨le_of_eq (by rw [ConZonotope.absorbRounding]; exact toReal_zero),
      le_of_eq (by rw [ConZonotope.absorbRounding]; exact toReal_zero.symm)⟩, add_zero x⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
