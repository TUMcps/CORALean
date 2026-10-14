module

public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.HybridDynamics.Operations.JumpIntersectionOfPoint
public import CORALean.HybridDynamics.Theorems.JumpOfPointOuter

@[expose] public section

/-!
# `Transition.jumpIntersectionOfPoint` contains the states that leave through the transition

`jumpOfPoint_outer` at `hinter := Intersection.intersection_outer R e.guard`, exactly as
`jumpIntersection_outer` reads `jump_outer` — the interface's guarantee is the
inclusion asked for, so no caller-supplied enclosure is needed here either.

And the same price: the guard is in the state's own family, `Intersection.intersection` having
nowhere else to put it (#39).
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes OfPoint
open scoped CORALean.Real

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump; the reset image then
lands in `jumpIntersectionOfPoint R`, the guard intersection computed rather than
assumed. -/
theorem Transition.jumpIntersectionOfPoint_outer [∀ n, Intersection (S n) (Vec ℝ n)]
    (e : Transition S L 𝕋 n) {R : S n} {z : Vec ℝ n} (hz : z ∈ construct R)
    (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpIntersectionOfPoint R) :=
  e.jumpOfPoint_outer (Intersection.intersection_outer R e.guard) hz hguard

/-- Anonymous, its content being that it elaborates (#38): `Real.ConPolyZono` has no
`Real.OfInterval` instance, yet this typechecks, and its `Intersection` is exact, so the
reset cuts a non-convex reachable set by its guard exactly. -/
example (e : Transition 𝒞𝒫𝒵 L ℝ n)
    (R : Real.ConPolyZono (Vec ℝ n))
    {z : Vec ℝ n} (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpIntersectionOfPoint R) :=
  e.jumpIntersectionOfPoint_outer hz hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
