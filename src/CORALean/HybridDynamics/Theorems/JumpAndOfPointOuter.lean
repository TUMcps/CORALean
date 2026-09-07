import CORALean.ContSet.ConPolyZono.Real.Instances
import CORALean.HybridDynamics.Operations.JumpAndOfPoint
import CORALean.HybridDynamics.Theorems.JumpOfPointOuter

/-!
# `Transition.jumpAndOfPoint` contains the states that leave through the transition

`jumpOfPoint_outer` at `hand := And.and_outer R e.guard`, exactly as
`jumpAnd_outer` reads `jump_outer` — the interface's guarantee is the
inclusion asked for, so no caller-supplied enclosure is needed here either.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfPoint

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump; the reset image then
lands in `jumpAndOfPoint R`, the guard intersection computed rather than
assumed. -/
theorem Transition.jumpAndOfPoint_outer [∀ n, And (S n) (Vec ℝ n)] (e : Transition S L 𝕋 n)
    {R : S n} {z : Vec ℝ n} (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpAndOfPoint R) :=
  e.jumpOfPoint_outer (And.and_outer R e.guard) hz hguard

/-- Anonymous, its content being that it elaborates (#38): `ConPolyZono` has no
`OfInterval` instance, yet this typechecks, and its `And` is exact, so the
reset cuts a non-convex reachable set by its guard exactly. -/
example (e : Transition (fun n => ConPolyZono (Vec ℝ n)) L ℝ n) (R : ConPolyZono (Vec ℝ n))
    {z : Vec ℝ n} (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpAndOfPoint R) :=
  e.jumpAndOfPoint_outer hz hguard

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
