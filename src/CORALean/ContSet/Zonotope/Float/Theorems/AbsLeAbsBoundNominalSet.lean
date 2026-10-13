import CORALean.ContSet.Zonotope.Float.Operations.Abs
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCornerMem
import CORALean.ContSet.Zonotope.Real.Theorems.AbsLeAbsBound

/-!
# The corner of `abs` bounds the nominal part

The corner bounds the entrywise absolute value of every point of the nominal part of `Z`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The corner bounds the entrywise absolute value of every point of the nominal part of `Z`. -/
theorem Zonotope.abs_le_absBound_of_mem_nominalSet (Z : Zonotope (Vec 𝕋 n)) {x : Vec ℝ n}
    (hx : x ∈ nominalSet Z) (j : Fin n) : |x j| ≤ (nominal Z).absBound j := by
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_nominalSet_iff.mp hx
  exact CORALean.Real.Zonotope.abs_le_absBound hβ hx j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
