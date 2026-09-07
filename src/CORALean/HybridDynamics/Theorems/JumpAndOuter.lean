import CORALean.HybridDynamics.Operations.JumpAnd
import CORALean.HybridDynamics.Theorems.JumpOuter

/-!
# `Transition.jumpAnd` contains the states that leave through the transition

`jump_outer` at `hand := And.and_outer R e.guard`: the interface's guarantee is
exactly the inclusion `jump_outer` asks for, so the guard intersection needs no
caller-supplied enclosure here, unlike at a representation with no `And`
instance.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable {𝕋 : Type} [Scalar 𝕋] [Mtimes (Mat 𝕋) S] [OfInterval S] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `R` encloses the state at the moment of the jump; the reset image then
lands in `jumpAnd R`, the guard intersection computed rather than assumed. -/
theorem Transition.jumpAnd_outer [∀ n, And (S n) (Vec ℝ n)] (e : Transition S L 𝕋 n)
    {R : S n} {z : Vec ℝ n} (hz : z ∈ construct R) (hguard : z ∈ construct e.guard) :
    e.reset z ∈ construct (e.jumpAnd R) :=
  e.jump_outer (And.and_outer R e.guard) hz hguard

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
