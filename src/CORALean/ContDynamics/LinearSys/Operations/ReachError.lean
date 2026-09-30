import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.ReachInputError
import CORALean.ContDynamics.LinearSysDT.Operations.ReachError

/-!
# What a sampled run owes, as a zonotope

The continuous-time run here is `LinearSysDT.reach` of the sampled system
`sys.discretize Δt`, with `inputSolution Δt η U` as every step's input set. It
loses ground in two places, and each has its own accumulated zonotope:

* the reductions, which `LinearSysDT.reachError` already accumulates;
* the input enclosures, each wider than what one held input contributes, which
  `reachInputError` accumulates the same way.

`reachError` is their sum. Both summands are zonotopes, so this is one too, and
`minkDiffRep` can take it off the run (`reachInnerRep`).
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `k` sampled steps owe: the reduction boxes and the input enclosures'
error boxes, each accumulated under `e^{AΔt}`. -/
noncomputable def LinearSys.reachError (sys : LinearSys 𝕋 n) (Δt : ℝ) (η o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : Zonotope (Vec ℝ n) :=
  ((sys.discretize Δt).reachError ⟨R₀, sys.inputSolution (S := 𝒵) Δt η U, 0, k⟩ ⟨o, ho⟩).plus
    (sys.reachInputError Δt η U k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
