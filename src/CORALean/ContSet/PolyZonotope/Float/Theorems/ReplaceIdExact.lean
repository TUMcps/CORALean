module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ReplaceId
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReplaceIdExact
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReplaceIdSubset

@[expose] public section

/-!
# An injective renaming changes nothing, in float too

Renaming factors injectively denotes the same set: equality, the error box as it was.
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

/-- An injective renaming denotes the same set. -/
theorem PolyZonotope.replaceId_exact (pZ : PolyZonotope (Vec 𝕋 n)) {p' : ℕ} (f : Fin pZ.p → Fin p')
    (hf : Function.Injective f) : (pZ.replaceId f).construct = pZ.construct := by -- --- PROOF ---
  have h : nominalSet (pZ.replaceId f) = ((nominal pZ).replaceId f).construct := rfl
  show nominalSet (pZ.replaceId f) + (pZ.replaceId f).err.construct
    = nominalSet pZ + pZ.err.construct
  rw [h]
  exact congrArg (· + pZ.err.construct) (Real.PolyZonotope.replaceId_exact (nominal pZ) f hf)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
