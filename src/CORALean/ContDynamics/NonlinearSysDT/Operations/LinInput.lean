import CORALean.ContSet.Conversion.Float.Interval_to_ContSet
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContDynamics.NonlinearSysDT.Definitions.LinStep

/-!
# The input set one discrete linearization step has to be given

`LinStep.linInput` widens `U` by the step's own certificate, as `NonlinearSys`'s
`linInput` does: the constant box `c`, `B(U ⊖ u✱)` and `L`. Nothing evaluates `f`:
the constant is the box the step carries, so it runs at a float scalar as it does
at `ℝ`. `u✱` is shifted out as a point box at `-u✱`, exact in either.
-/

-- Authors:       Claude Sonnet 5
-- Written:       04-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes CORALean.Float OfInterval

variable {n m : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] [OfInterval S 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The input set this step's linear system has to be given. -/
def NonlinearSysDT.LinStep.linInput {sys : NonlinearSysDT n m} {U : S m}
    (step : sys.LinStep 𝕋 U) : S n :=
  let negUs := Interval.point fun i => FloatOps.neg (step.us i)       -- the box at `-u✱`
  ofInterval step.c ⊞ mtimes (𝕄 := Mat 𝕋) step.B (U ⊞ ofInterval negUs) ⊞ step.L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
