import CORALean.ContSet.Zonotope.Float.Operations.Recentre
import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

/-!
# `Zonotope.recentre` holds the origin

The nominal part at the zero coefficients is the zeroed centre, and the widened
box holds `0` by construction.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zero_mem_recentre (Z : Zonotope 𝕋 n) :
    (0 : Vec ℝ n) ∈ Z.recentre.construct := by -- --- PROOF ---
  refine ⟨0, Zonotope.mem_nominalSet_iff.mpr ⟨0, fun j => by simp, fun i => ?_⟩, 0,
    fun i => ?_, add_zero 0⟩
  · simp [Zonotope.recentre, toReal_zero]
  · show toReal (minimum (Z.E.inf i) zero) ≤ 0 ∧ 0 ≤ toReal (maximum (Z.E.sup i) zero)
    rw [toReal_minimum, toReal_maximum, toReal_zero]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
