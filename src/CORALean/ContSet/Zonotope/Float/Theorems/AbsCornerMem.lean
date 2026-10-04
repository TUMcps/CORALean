import CORALean.ContSet.Zonotope.Float.Operations.Abs
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Zonotope.Real.Theorems.AbsCornerMem
import CORALean.ContSet.Zonotope.Float.Theorems.AbsCornerMemNominalSet

/-!
# The corner of `abs` is a point of `abs Z`

Inner: the corner `|c| + Σ |gⱼ|` of the stored floats is a point of `abs Z` once its error box
holds `0`. Like the real one this is not an enclosure of the input.
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

/-- Inner: the corner is a point of `abs Z` when the error box holds `0`. -/
theorem Zonotope.abs_corner_mem_construct (Z : Zonotope 𝕋 n)
    (h0 : ∀ i, toReal (Z.E.inf i) ≤ 0 ∧ 0 ≤ toReal (Z.E.sup i)) :
    (fun i => (nominal Z).absBound i) ∈ Z.abs.construct :=
  ⟨_, Zonotope.abs_corner_mem_nominalSet Z, 0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
