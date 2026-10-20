module

public import CORALean.HybridDynamics.Operations.Jump

@[expose] public section

/-!
# `Transition.jumpIntersection`

`Transition.jump` with the guard intersection computed rather than assumed:
`Intersection.intersection` cuts `R` down to what meets `e.guard`, and the reset propagates over
that result as `jump` propagates it over any enclosure. A representation with no `Intersection`
instance still calls `jump` and supplies `hinter` itself. The guard has to live in the state's own
family, so the transition is `Transition S L 𝕋 n`, not the general `Transition G L 𝕋 n` (#39).

## Inputs
* `e` – transition
* `R` – reach set

## Output
* image of the guard intersection under the reset
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Mtimes Real.OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [Real.OfInterval S] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `jump`, with the incoming enclosure cut to the guard by
`Intersection.intersection` first. -/
def Transition.jumpIntersection [∀ n, Intersection (S n) (Vec ℝ n)]
    (e : Transition S L 𝕋 n) (R : S n) : S n :=
  e.jump (Intersection.intersection R e.guard)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
