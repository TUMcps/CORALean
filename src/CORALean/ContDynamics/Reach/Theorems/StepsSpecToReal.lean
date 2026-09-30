import CORALean.ContDynamics.Reach.Theorems.StepsSpec
import CORALean.Global.Float.ToRat

/-!
# `Reach.steps` at a float time step, read in ℝ

What a float run needs of the step count it derived: `timeStep` denotes a
positive real, and `N` of it span the horizon exactly, in the reals the
guarantees are stated in. `ToRat.toReal_toRat` carries `steps_spec` across.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic


-- =======================================  MAIN THEOREM  ======================================= --

theorem Reach.steps_spec_toReal {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    {tStart tFinal : ℚ} {timeStep : 𝕋} {N : ℕ}
    (h : Reach.steps tStart tFinal (ToRat.toRat timeStep) = some N) :
    0 < toReal timeStep ∧ (N : ℝ) * toReal timeStep = (tFinal : ℝ) - tStart := by -- --- PROOF ---
  obtain ⟨hpos, hN⟩ := Reach.steps_spec h
  rw [← ToRat.toReal_toRat]
  refine ⟨Rat.cast_pos.mpr hpos, ?_⟩
  -- cast the exact identity in ℚ into ℝ
  exact_mod_cast hN

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
