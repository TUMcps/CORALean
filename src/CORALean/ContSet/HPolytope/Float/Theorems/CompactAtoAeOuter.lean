import CORALean.ContSet.HPolytope.Float.Operations.CompactAtoAe
import CORALean.ContSet.HPolytope.Float.Theorems.PairsToEqExact
import CORALean.ContSet.HPolytope.Float.Theorems.NormalizeRowsOuter

/-!
# The float `compactAtoAe` keeps every point of the polytope in the domain

`pairsToEq` is exact (`pairsToEq_exact`), so what is left of the outer statement is the
normalization's (`normalizeRows_outer`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactAtoAe_outer (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n))
    (dom : Interval (Vec 𝕋 n)) :
    P.construct ∩ dom.construct ⊆
      (P.compactAtoAe p dom).construct ∩ dom.construct := by
  intro x hx
  have h := HPolytope.normalizeRows_outer p P dom hx
  unfold HPolytope.compactAtoAe
  rwa [HPolytope.pairsToEq_exact]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
