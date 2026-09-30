import CORALean.ContDynamics.LinearSys.Definitions.ReachStepOptions
import CORALean.ContDynamics.LinearSys.Operations.Reach
import CORALean.ContDynamics.LinearSys.Operations.ReachOrder

/-!
# `reach` at an order raised until admissible

`η = options.taylorTerms` is the order asked for, raised to `reachOrder Δt + 2` where that
is higher, the same raise `reachWrappingFree` runs: `reach_outer` needs an order admissible
for `Δt` and `sys.A`, and `ReachStepOptions` has no field for it, the matrix not
being there to decide it. `LinearSys.reachInstance` runs this instead of `reach`
itself, so it asks its caller for no side condition on `η` at all.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One time-interval set per window `τ_k`, `k < ⌈(tFinal - tStart) / Δt⌉`, at order `η`
raised until admissible. -/
noncomputable def LinearSys.reachAdmissible (sys : LinearSys 𝕋 n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachStepOptions ℝ) : SetUnion (S n) :=
  let Δt := options.timeStep
  let η := options.taylorTerms
  let η' := max η (sys.reachOrder Δt + 2)                        -- η, raised until admissible
  sys.reach params ⟨Δt, η'⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
