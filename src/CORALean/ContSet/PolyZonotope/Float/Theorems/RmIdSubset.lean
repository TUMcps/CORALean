import CORALean.ContSet.PolyZonotope.Float.Operations.RmId
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.RmIdConstruct
import CORALean.ContSet.PolyZonotope.Float.Theorems.RmIdConstruct

/-!
# `rmId` gives a subset, in float too

Inner: the set with the removed factors pinned lies in the original.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inner: the pinned set lies in the original. -/
theorem PolyZonotope.rmId_subset (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    (pZ.rmId S).construct ⊆ pZ.construct := by
  rw [PolyZonotope.rmId_construct]
  rintro _ ⟨_, ⟨a, β, ha, _, hβ, rfl⟩, e, he, rfl⟩
  exact ⟨_, ⟨a, β, ha, hβ, rfl⟩, e, he, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
