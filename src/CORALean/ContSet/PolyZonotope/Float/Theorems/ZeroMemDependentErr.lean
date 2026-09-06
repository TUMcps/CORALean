import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent

/-!
# `dependent`'s error box denotes the origin alone

So nothing is left outside its nominal set.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result's box denotes the origin alone, so nothing is left outside its
nominal set. -/
theorem PolyZonotope.zero_mem_dependent_err (PZ : PolyZonotope 𝕋 n) :
    (0 : Vec ℝ n) ∈ (PZ.dependent.err).construct := fun i =>
  ⟨le_of_eq (by rw [PolyZonotope.dependent]; exact toReal_zero),
   le_of_eq (by rw [PolyZonotope.dependent]; exact toReal_zero.symm)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
