import CORALean.ContSet.Zonotope.Float.Operations.Underapproximate
import CORALean.ContSet.Zonotope.Float.Theorems.ContainsPointSound

/-!
# `Zonotope.underapproximate` returns points of the zonotope

A returned point passed `Zonotope.containsPoint`, so it is a member (`containsPoint_sound`). Inner
only: no claim that it is the vertex `c ± Σⱼ sign(sᵀ gⱼ) gⱼ` of the real definition.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.underapproximate_inner {Z : Zonotope (Vec 𝕋 n)} {H : Mat 𝕋 Z.h n} {s : Vec 𝕋 n}
    {b : Bool} {p : Vec 𝕋 n} (h : Z.underapproximate H s b = some p) :
    toRealVec p ∈ Z.construct := by
  unfold Zonotope.underapproximate at h
  dsimp only at h
  split_ifs at h with hc
  · cases h; exact Zonotope.containsPoint_sound hc

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
