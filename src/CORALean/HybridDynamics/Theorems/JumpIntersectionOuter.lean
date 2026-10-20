module

public import CORALean.HybridDynamics.Operations.JumpIntersection
public import CORALean.HybridDynamics.Theorems.JumpOuter

@[expose] public section

/-!
# `Transition.jumpIntersection` contains what leaves through the transition

`jump_outer` at `hinter := Intersection.intersection_outer R e.guard`: the interface's guarantee is
exactly the inclusion `jump_outer` asks for, so the guard intersection needs no caller-supplied
enclosure here. The enclosed intersection with a guard is the second half of [1, Alg. 1]
(`timeIntervalInv_outer` is the first). The price is that `Intersection.intersection` takes two
sets of one type, so the guard is asked to be in the state's own family: `Transition S L 𝕋 n`
(#39).

## Inputs
* `e` – transition
* `R` – set holding the state at the jump
* `z` – state at the jump

## Hypotheses
* `hz` – state lies in the reach set
* `hguard` – state lies in the guard

## Conclusion
* reset image lies in the jump image

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
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
