import CORALean.ContSet.PolyZonotope.Float.Operations.RmId
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet
import CORALean.ContSet.PolyZonotope.Real.Theorems.RmIdConstruct

/-!
# `rmId` pins the removed factors at `1`, in float too

The stored floats are untouched and the nominal part is the exact layer's `rmId` of the original's,
so the exact theorem carries over with the error box as it was.
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

theorem PolyZonotope.rmId_construct (pZ : PolyZonotope (Vec 𝕋 n)) (S : Finset (Fin pZ.p)) :
    (pZ.rmId S).construct
      = {x | ∃ (a : Fin pZ.p → ℝ) (β : Fin pZ.q → ℝ), (∀ k, |a k| ≤ 1) ∧ (∀ k ∈ S, a k = 1)
          ∧ (∀ j, |β j| ≤ 1) ∧ x = (nominal pZ).point a + ∑ j, β j • (nominal pZ).GI j}
        + pZ.err.construct := by
  have h : nominalSet (pZ.rmId S) = ((nominal pZ).rmId S).construct := rfl
  show nominalSet (pZ.rmId S) + (pZ.rmId S).err.construct = _
  rw [h, Real.PolyZonotope.rmId_construct (nominal pZ) S]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
