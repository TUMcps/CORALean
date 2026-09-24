import CORALean.ContDynamics.LinearSys.Definitions.ReachParams
import CORALean.ContDynamics.LinearSys.Operations.ReachOrder
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `timeIntervalStep`, packaged as `Reach`'s `SetUnion`

One branch, `sys.timeIntervalStep p.r` at `reachOrder`'s own order — the
`Reach.reach` field of the instance. A single step covers the whole window,
so `Δt` plays no part: subdividing it is what `manualStep`/`tunedStep` are
for, and neither is written generically over `S`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
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

/-- One branch, `sys.timeIntervalStep p.r` at `reachOrder`'s own order. -/
noncomputable def LinearSys.reachUnion (sys : LinearSys 𝕋 n) (p : LinearSys.ReachParams)
    (X₀ : S n) : SetUnion (S n) :=
  ⟨[sys.timeIntervalStep p.r (sys.reachOrder p.r + 2) X₀]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
