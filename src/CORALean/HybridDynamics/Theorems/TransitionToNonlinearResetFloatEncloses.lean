module

public import CORALean.HybridDynamics.Operations.TransitionToNonlinearResetFloat
public import CORALean.HybridDynamics.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint

@[expose] public section

/-!
# The float model of an affine reset encloses it

The interval extension `toNonlinearResetFloat` of a transition's affine reset encloses the real
reset `x ↦ W x + w` the stored coefficients denote, over any boxes.

## Inputs
* `e` – transition

## Hypotheses
* none

## Conclusion
* the float model encloses the affine reset
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
