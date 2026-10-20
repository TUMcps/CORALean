module

public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Point
public import CORALean.HybridDynamics.Definitions.Transition

@[expose] public section

/-!
# `Transition.jump`

The reset propagated over a set: `mtimes` for the matrix, `plus` for the offset. The argument is
the set already cut down by the guard, so the guard's representation `G` never enters;
`JumpOuter` takes an enclosure of the intersection as its one hypothesis, and `JumpIntersection`
is the call site that supplies `Intersection.intersection`. The offset enters as a box of zero
width through `OfInterval`, which keeps `ConPolyZono` out. `W` and `w` are read through
`Scalar 𝕋`, so `OfInterval` here is the exact layer's, whatever `𝕋` stores.

## Inputs
* `e` – transition
* `Rg` – set cut by the guard

## Output
* image of the set under the reset
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [Real.OfInterval S] {G : ℕ → Type}
variable {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Transition.jump (e : Transition G L 𝕋 n) (Rg : S n) : S n :=
  plus (mtimes e.W Rg) (ofInterval (Real.Interval.point (toRealVec e.w)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
