import CORALean.HybridDynamics.Operations.Jump

/-!
# `Transition.jumpIntersection`

`Transition.jump` with the guard intersection computed rather than assumed:
`Intersection.intersection` cuts `R` down to what meets `e.guard`, and the reset
propagates over that result exactly as `jump` propagates it over any enclosure.

`jump_outer`'s `hinter` bargain stays untouched — a representation with no
`Intersection` instance still calls `jump` directly and supplies `hinter`
itself. This is the case where the interface discharges it.

`Intersection.intersection` takes two sets of *one* type, so this is the one
place where the guard has to live in the state's own family: the transition here
is `Transition S L 𝕋 n`, not the general `Transition G L 𝕋 n` (#39).
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


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
