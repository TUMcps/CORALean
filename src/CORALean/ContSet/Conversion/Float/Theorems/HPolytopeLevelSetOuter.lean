module

public import CORALean.ContSet.Conversion.Float.Theorems.HPolytopeLevelSetExact
public import CORALean.ContSet.HPolytope.Float.Theorems.AbsorbRoundingOuter

@[expose] public section

/-!
# A float polytope with an error box, as a level set, from outside

`levelSet` reads the rows, not the box. A polytope with a box is converted after its box has been
folded into its rows: the result contains the polytope. For an error-free one the rows are the
set (`levelSet_exact`).

## Inputs
* `P` – halfspace polytope

## Hypotheses
* none

## Conclusion
* polytope is contained in the level set of its rounding-absorbed form
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.levelSet_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) :
    P.construct ⊆ P.absorbRounding.levelSet.construct := by
  rw [HPolytope.levelSet_exact]
  intro x hx
  exact (HPolytope.mem_nominal_of_origin (P := P.absorbRounding) rfl).mp
    (HPolytope.absorbRounding_outer P hx)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
