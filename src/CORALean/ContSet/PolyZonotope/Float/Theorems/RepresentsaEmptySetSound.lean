import CORALean.ContSet.PolyZonotope.Float.Operations.RepresentsaEmptySet
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.Interval.Float.Theorems.RepresentsaEmptySetSound

/-!
# `PolyZonotope.representsa_emptySet` is sound

`representsa_emptySet = true` means the set is empty: the error box is.
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

theorem PolyZonotope.representsa_emptySet_sound {pZ : PolyZonotope (Vec 𝕋 n)}
    (h : pZ.representsa_emptySet = true) : pZ.construct = ∅ := by
  have hE := Interval.representsa_emptySet_sound h
  show nominalSet pZ + pZ.err.construct = ∅
  rw [hE, Set.add_empty]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
