module

public import CORALean.ContSet.PolyZonotope.Float.Operations.RmId
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RmIdToSet
public import CORALean.ContSet.PolyZonotope.Float.Theorems.RmIdToSet

@[expose] public section

/-!
# `rmId` gives a subset, in float too

Inner: the set with the removed factors pinned lies in the original.

## Inputs
* `pZ` – polynomial zonotope
* `S` – factors to remove

## Hypotheses
* none

## Conclusion
* the result is contained in the original set
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inner: the pinned set lies in the original. -/
theorem PolyZonotope.rmId_subset (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    (pZ.rmId S).toSet ⊆ pZ.toSet := by
  rw [PolyZonotope.rmId_toSet]
  rintro _ ⟨_, ⟨a, β, ha, _, hβ, rfl⟩, e, he, rfl⟩
  exact ⟨_, ⟨a, β, ha, hβ, rfl⟩, e, he, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
