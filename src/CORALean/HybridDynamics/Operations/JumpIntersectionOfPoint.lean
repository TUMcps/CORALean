import CORALean.HybridDynamics.Operations.JumpOfPoint

/-!
# `Transition.jumpIntersectionOfPoint`

`jumpOfPoint` with the guard intersection computed rather than assumed, exactly
as `jumpIntersection` is `jump` with it. At `ConPolyZono`, whose `Intersection`
is exact and whose only offset ask is `OfPoint`, this is what cuts a non-convex
reachable set by a guard exactly — the payoff `OfPoint` exists for.

As at `jumpIntersection`, `Intersection.intersection` is homogeneous, so the
guard is asked to be in the state's own family here and nowhere else (#39).
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes OfPoint

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `jumpOfPoint`, with the incoming enclosure cut to the guard by `Intersection.intersection`
first. -/
def Transition.jumpIntersectionOfPoint [∀ n, Intersection (S n) (Vec ℝ n)]
    (e : Transition S L 𝕋 n) (R : S n) : S n :=
  e.jumpOfPoint (Intersection.intersection R e.guard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
