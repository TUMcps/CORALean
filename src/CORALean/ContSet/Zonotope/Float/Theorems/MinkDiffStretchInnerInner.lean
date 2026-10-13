import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffStretchInner
import CORALean.ContSet.Zonotope.Float.Theorems.ContainsZonotopeSound
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

/-!
# The float `minkDiffStretchInner` is an inner approximation

A returned zonotope `D` passed `containsZonotope` on `D + Z₂` against `Z₁`: the float sum
encloses `D + Z₂` (`plus_outer`), and the check puts that sum inside `Z₁`
(`containsZonotope_sound`). So every point of `D` has all of `Z₂` added into `Z₁`, which is
membership in the Minkowski difference — the float counterpart of
`Real.Zonotope.minkDiffStretch_inner`, with the check in place of [1, Thm. 4]'s constraint on
`μ`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffStretchInner_inner {Z₁ Z₂ D : Zonotope (Vec 𝕋 n)} {μ : Fin Z₁.h → 𝕋}
    {H : Mat 𝕋 Z₁.h n} (h : Z₁.minkDiffStretchInner Z₂ μ H = some D) :
    D.construct ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  unfold Zonotope.minkDiffStretchInner at h
  dsimp only at h
  split_ifs at h with hc
  cases h
  intro x hx y hy
  exact Zonotope.containsZonotope_sound hc
    (Zonotope.plus_outer _ _ (Set.add_mem_add hx hy))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
