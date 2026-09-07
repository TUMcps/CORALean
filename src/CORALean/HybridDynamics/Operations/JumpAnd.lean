import CORALean.HybridDynamics.Operations.Jump

/-!
# `Transition.jumpAnd`

`Transition.jump` with the guard intersection computed rather than assumed:
`And.and` cuts `R` down to what meets `e.guard`, and the reset propagates over
that result exactly as `jump` propagates it over any enclosure.

`jump_outer`'s `hand` bargain stays untouched — a representation with no `And`
instance still calls `jump` directly and supplies `hand` itself. This is the
case where the interface discharges it.

`And.and` takes two sets of *one* type, so this is the one place where the
guard has to live in the state's own family: the transition here is
`Transition S L 𝕋 n`, not the general `Transition G L 𝕋 n` (#39).
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [OfInterval S] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `jump`, with the incoming enclosure cut to the guard by `And.and` first. -/
def Transition.jumpAnd [∀ n, And (S n) (Vec ℝ n)] (e : Transition S L 𝕋 n) (R : S n) : S n :=
  e.jump (And.and R e.guard)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
