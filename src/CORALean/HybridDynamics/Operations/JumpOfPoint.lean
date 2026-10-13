import CORALean.ContSet.ConPolyZono.Real.Instances
import CORALean.ContSet.ContSet.ContSet
import CORALean.HybridDynamics.Definitions.Transition

/-!
# `Transition.jump`, asking only for a singleton

`Transition.jump` reaches for `OfInterval` only to build `Interval.point w`, a
box of zero width. `OfPoint` says the same thing directly: the reset adds a
fixed vector, and nothing about that needs a general interval to be
convertible. This is additive — `jump` stays as it is, so a representation
with `OfInterval` keeps its existing route, and one with only `OfPoint`, such
as `ConPolyZono`, gains this one instead.

With `ConPolyZono.ofPoint` and its `Intersection` instance, `Transition.jumpIntersectionOfPoint`
now cuts a non-convex reachable set by a guard exactly. The guard's own
representation `G` is not read here either, so this asks nothing of it.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar Plus Mtimes OfPoint

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable {G : ℕ → Type} {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Transition.jumpOfPoint (e : Transition G L 𝕋 n) (Rg : S n) : S n :=
  plus (mtimes e.W Rg) (ofPoint (toRealVec e.w))

/-- Anonymous, its content being that it elaborates (#38): `ConPolyZono` has no
`OfInterval` instance, so `jump` is unavailable to it, and `jumpOfPoint`
above is what fills the gap. -/
example (e : Transition 𝒞𝒫𝒵 L ℝ n) (Rg : ConPolyZono (Vec ℝ n)) : ConPolyZono (Vec ℝ n) :=
  e.jumpOfPoint (S := 𝒞𝒫𝒵) Rg

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
