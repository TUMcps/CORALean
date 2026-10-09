import CORALean.ContSet.Zonotope.Float.Operations.MinkDiffRep
import CORALean.ContSet.Zonotope.Float.Theorems.ContainsZonotopeSound
import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter

/-!
# The float `minkDiffRep` is an inner approximation

A returned zonotope `D` passed `containsZonotope` on `D + Z₂` against `Z₁`: the float sum
encloses `D + Z₂` (`plus_outer`), and the check puts that sum inside `Z₁`
(`containsZonotope_sound`). So every point of `D` has all of `Z₂` added into `Z₁`, which is
membership in the Minkowski difference. Inner only, the direction `MinkDiff` owes: no claim that it
is `Real.Zonotope.minkDiffRep`'s result.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minkDiffRep_inner {Z₁ Z₂ D : Zonotope 𝕋 n} {M : Fin Z₁.h → Fin Z₂.h → 𝕋}
    {ρ : 𝕋} {H : Mat 𝕋 Z₁.h n} (h : Z₁.minkDiffRep Z₂ M ρ H = some D) :
    D.construct ⊆ minkowskiDiff Z₁.construct Z₂.construct := by -- --- PROOF ---
  unfold Zonotope.minkDiffRep at h
  dsimp only at h
  split_ifs at h with hc
  cases h
  intro x hx y hy
  exact Zonotope.containsZonotope_sound hc
    (Zonotope.plus_outer _ _ (Set.add_mem_add hx hy))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
