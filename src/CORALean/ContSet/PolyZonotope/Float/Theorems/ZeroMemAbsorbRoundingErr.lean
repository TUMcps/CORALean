module

public import CORALean.ContSet.PolyZonotope.Float.Operations.AbsorbRounding

@[expose] public section

/-!
# `absorbRounding`'s error box denotes the origin alone

So nothing is left outside its nominal set.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result's box denotes the origin alone, so nothing is left outside its
nominal set. -/
theorem PolyZonotope.zero_mem_absorbRounding_err (pZ : PolyZonotope (Vec 𝕋 n)) :
    (0 : Vec ℝ n) ∈ (pZ.absorbRounding.I_error).construct := fun i =>
  ⟨le_of_eq (by rw [PolyZonotope.absorbRounding]; exact toReal_zero),
   le_of_eq (by rw [PolyZonotope.absorbRounding]; exact toReal_zero.symm)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
