import CORALean.ContDynamics.LinearSys.Operations.Discretize
import CORALean.ContDynamics.LinearSys.Operations.StepErrorBox
import CORALean.ContSet.Zonotope.Real.Instances

/-!
# What a sampled run's input enclosures owe

A run of `(sys.discretize Δt).reach` adds `inputSolution Δt η U` at every step,
and that enclosure reaches past what one held input contributes by at most
`timePointStepErrorBox` (`inputSolution_subset_constInput_add_errorBox`). The
excess is paid afresh at every step and then carried along by the dynamics, so
a box paid at step `j` reaches step `k` multiplied by `e^{AΔt}` exactly
`k - 1 - j` times.

The counterpart of `LinearSysDT.reachError`, which accumulates the reduction
boxes by the same recursion; `reachError` in this directory adds the two.
Nothing here is reduced, so the generator count grows by `n` per step.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the input enclosures of `k` sampled steps owe together: every step's
error box, each carried forward by one `e^{AΔt}` per step taken since. -/
noncomputable def LinearSys.reachInputError (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ)
    (U : Zonotope (Vec ℝ n)) : ℕ → Zonotope (Vec ℝ n)
  | 0 => Zonotope.ofPoint 0
  | k + 1 => (Zonotope.mtimes (sys.discretize Δt).A (sys.reachInputError Δt η U k)).plus
      (sys.timePointStepErrorBox Δt η U)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
