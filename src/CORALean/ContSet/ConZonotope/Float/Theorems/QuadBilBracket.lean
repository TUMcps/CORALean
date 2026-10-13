import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilUp
import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp

/-!
# The two roundings bracket the bilinear form

`quadBilDown` and `quadBilUp` enclose `u ⬝ᵥ (Q *ᵥ v)` read back through `toReal`: each entry of
`Q *ᵥ v` is bracketed by `mulVecDown` and `mulVecUp`, and the per-term minima and maxima of
`PolyZonotope.quadDown` and `quadUp` then bracket the sum whichever sign `u` has.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.quadBil_bracket (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) :
    toReal (ConZonotope.quadBilDown Q u v)
        ≤ toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v)
      ∧ toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v)
        ≤ toReal (ConZonotope.quadBilUp Q u v) := by -- --- PROOF ---
  -- each entry of `Q *ᵥ v` between its two directed dot products
  have hw : ∀ r, toReal (mulVecDown Q v r) ≤ (toRealMat Q *ᵥ toRealVec v) r
      ∧ (toRealMat Q *ᵥ toRealVec v) r ≤ toReal (mulVecUp Q v r) := fun r =>
    ⟨dotDown_le (Q r) v, le_dotUp (Q r) v⟩
  exact ⟨PolyZonotope.quadDown_le hw, PolyZonotope.le_quadUp hw⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
