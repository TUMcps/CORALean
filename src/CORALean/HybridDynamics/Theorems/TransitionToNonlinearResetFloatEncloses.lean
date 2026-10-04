import CORALean.HybridDynamics.Operations.TransitionToNonlinearResetFloat
import CORALean.HybridDynamics.Operations.TransitionToNonlinearReset
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
import CORALean.ContSet.Interval.Float.Theorems.MemPoint

/-!
# The float model of an affine reset encloses it

The interval extension `toNonlinearResetFloat` of a transition's affine reset encloses the real
reset `x ↦ W x + w` the stored coefficients denote, over any boxes.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix CORALean.Float ContSet SoundFloatArithmetic

variable {G : ℕ → Type} {L : Type} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Transition.toNonlinearResetFloat_encloses (e : Transition G L 𝕋 n) :
    e.toNonlinearResetFloat.Encloses e.toNonlinearReset where
  f_mem X _ x hx _ _ :=
    Interval.plus_outer _ _ ⟨_, Interval.mtimes_outer e.W X ⟨x, hx, rfl⟩, _,
      Interval.mem_point e.w, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
