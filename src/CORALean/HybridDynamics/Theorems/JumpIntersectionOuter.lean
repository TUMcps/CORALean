import CORALean.HybridDynamics.Operations.JumpIntersection
import CORALean.HybridDynamics.Theorems.JumpOuter

/-!
# `Transition.jumpIntersection` contains what leaves through the transition

`jump_outer` at `hinter := Intersection.intersection_outer R e.guard`: the
interface's guarantee is exactly the inclusion `jump_outer` asks for, so the
guard intersection needs no caller-supplied enclosure here, unlike at a
representation with no `Intersection` instance.

The enclosed intersection with a guard, the second half of [1, Alg. 5] —
`timeIntervalInv_outer` is the first.

The price is that `Intersection.intersection` takes two sets of one type, so the
guard is asked to be in the state's own family here: `Transition S L 𝕋 n` (#39).

It is also the last line of [2, Alg. 1].

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [Real.OfInterval S] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump; the reset image then lands
in `jumpIntersection R`, the guard intersection computed rather than assumed. -/
theorem Transition.jumpIntersection_outer [∀ n, Intersection (S n) (Vec ℝ n)]
    (e : Transition S L 𝕋 n) {R : S n} {z : Vec ℝ n} (hz : z ∈ construct R)
    (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpIntersection R) :=
  e.jump_outer (Intersection.intersection_outer R e.guard) hz hguard

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
