import CORALean.ContSet.Zonotope.Float.Operations.ReduceUnderApprox
import CORALean.ContSet.Zonotope.Float.Theorems.ContainsZonotopeSound

/-!
# `Zonotope.reduceUnderApprox` is inner

A returned zonotope passed `Zonotope.containsZonotope`, so its set lies in the input's
(`containsZonotope_sound`). Inner only: nothing is claimed about order or optimality.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceUnderApprox_inner
    {opt : (Z : Zonotope (Vec 𝕋 n)) → Option (Σ h : ℕ, Mat 𝕋 n h)} {Z : Zonotope (Vec 𝕋 n)}
    {H : Mat 𝕋 Z.h n} {R : Zonotope (Vec 𝕋 n)} (h : Zonotope.reduceUnderApprox opt Z H = some R) :
    R.construct ⊆ Z.construct := by -- --- PROOF ---
  unfold Zonotope.reduceUnderApprox at h
  dsimp only at h
  split at h
  · split_ifs at h with h1
    cases h; exact Zonotope.containsZonotope_sound h1
  · split_ifs at h with h1 h2
    · cases h; exact Zonotope.containsZonotope_sound h1
    · cases h; exact Zonotope.containsZonotope_sound h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
