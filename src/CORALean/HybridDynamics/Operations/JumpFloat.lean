module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.HybridDynamics.Definitions.Transition
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# `Transition.jumpFloat`

`Transition.jump` at a float zonotope: the reset `x ↦ W x + w` propagated by
`mtimes` for the matrix and `plus` for the offset. `jump` reaches the offset
through `Real.OfInterval`, which no float representation has; here `w` is
stored floats already, so the box of zero width at it is a float box, and
`Interval.zonotope` turns it into a zonotope with nothing to round.

As at `jump`, the argument is the set already cut to the guard, so the guard's
representation `G` is not read here.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {G : ℕ → Type} {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reset image `W Rg ⊕ {w}` of the guard-cut set `Rg`. -/
def Transition.jumpFloat (e : Transition G L 𝕋 n) (Rg : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) e.W Rg ⊞
    (Interval.point e.w).zonotope

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
