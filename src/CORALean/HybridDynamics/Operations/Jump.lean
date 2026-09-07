import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.HybridDynamics.Transition

/-!
# `Transition.jump`

The reset propagated over a set: `mtimes` for the matrix, `plus` for the offset,
which is `Layer.linear` at a square matrix and for the same reason — a
representation closed under both loses nothing here.

The argument is the set *already cut down by the guard*, so the guard's own
representation `G` never enters here at all. Intersecting would tie this
definition to `And`, which not every representation instantiates, so `JumpOuter`
takes an enclosure of the intersection as its one hypothesis instead; `JumpAnd`
is the call site that supplies `And.and` where one exists.

The offset enters as a box of zero width through `OfInterval`, so no translation
operation is needed — and that is what keeps `ConPolyZono` out, having `plus`
and `mtimes` but no `OfInterval` instance.

`W` and `w` are read through `Scalar 𝕋`, so `mtimes` and `Interval.point` see
what they denote: `OfInterval` here is the exact layer's, whatever `𝕋` stores.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [OfInterval S] {G : ℕ → Type} {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Transition.jump (e : Transition G L 𝕋 n) (Rg : S n) : S n :=
  plus (mtimes e.W Rg) (ofInterval (Interval.point (toRealVec e.w)))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
