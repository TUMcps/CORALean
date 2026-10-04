import CORALean.ContSet.PolyZonotope.Float.Operations.ReplaceId
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReplaceIdExact

/-!
# Renaming factors can only shrink the set, in float too

The stored floats are untouched and the nominal part is the exact layer's `replaceId` of the
original's: the renamed set lies in the original (inner), the error box as it was.
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

/-- Inner: the renamed set lies in the original. -/
theorem PolyZonotope.replaceId_subset (pZ : PolyZonotope 𝕋 n) {p' : ℕ} (f : Fin pZ.p → Fin p') :
    (pZ.replaceId f).construct ⊆ pZ.construct := by
  have h : nominalSet (pZ.replaceId f) = ((nominal pZ).replaceId f).construct := rfl
  rintro _ ⟨y, hy, e, he, rfl⟩
  rw [h] at hy
  exact ⟨y, Real.PolyZonotope.replaceId_subset (nominal pZ) f hy, e, he, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
