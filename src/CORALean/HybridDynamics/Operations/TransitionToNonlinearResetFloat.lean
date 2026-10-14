module

public import CORALean.HybridDynamics.Definitions.NonlinearResetFloatModel
public import CORALean.HybridDynamics.Definitions.Transition
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The affine reset of a transition as a float model

`Transition.toNonlinearResetFloat`: the interval extension of `x ↦ W x + w` of a transition's
stored float coefficients, `W X ⊕ w` in directed rounding, independent of the (empty) input.
That it encloses the real reset is `toNonlinearResetFloat_encloses`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {G : ℕ → Type} {L : Type} {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval extension of the affine reset. -/
def Transition.toNonlinearResetFloat (e : Transition G L 𝕋 n) :
    NonlinearReset.FloatModel 𝕋 n 0 n where
  f := fun X _ => (Interval.mtimes e.W X).plus (Interval.point e.w)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
