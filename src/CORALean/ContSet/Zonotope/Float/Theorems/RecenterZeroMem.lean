module

public import CORALean.ContSet.Zonotope.Float.Operations.Recenter
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# `Zonotope.recenter` holds the origin

The nominal part at the zero coefficients is the zeroed center, and the widened
box holds `0` by construction.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* origin lies in the recentered zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.zero_mem_recenter (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (0 : Vec ℝ n) ∈ Z.recenter.construct := by -- --- PROOF ---
  refine ⟨0, Zonotope.mem_nominalSet_iff.mpr ⟨0, fun j => by simp, fun i => ?_⟩, 0,
    fun i => ?_, add_zero 0⟩
  · simp [Zonotope.recenter, toReal_zero]
  · show toReal (minimum (Z.I_error.inf i) zero) ≤ 0 ∧ 0 ≤ toReal (maximum (Z.I_error.sup i) zero)
    rw [toReal_minimum, toReal_maximum, toReal_zero]
    exact ⟨min_le_right _ _, le_max_right _ _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
