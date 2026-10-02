import CORALean.ContSet.HPolytope.Float.Operations.EmptySet
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `HPolytope.emptySet` denotes `∅`

The one row reads `0 ≤ -1`, which no point satisfies.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.construct_emptySet : (HPolytope.emptySet 𝕋 n).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h : (toRealMat (HPolytope.emptySet 𝕋 n).A *ᵥ x) (0 : Fin 1)
      ≤ toReal ((HPolytope.emptySet 𝕋 n).b (0 : Fin 1)) :=
    (HPolytope.mem_construct_iff.mp hx).1 (0 : Fin 1)
  have h0 : (toRealMat (HPolytope.emptySet 𝕋 n).A *ᵥ x) (0 : Fin 1) = 0 := by
    simp [Matrix.mulVec, dotProduct, toRealMat, HPolytope.emptySet, toReal_zero]
  have h1 : toReal ((HPolytope.emptySet 𝕋 n).b (0 : Fin 1)) = -1 := by
    simp [HPolytope.emptySet, toReal_neg, toReal_one]
  rw [h0, h1] at h
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
