module

public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.ReachInputError
public import CORALean.ContDynamics.LinearSysDT.Operations.ReachError

@[expose] public section

/-!
# What a sampled run owes, as a zonotope

The continuous-time run here is `LinearSysDT.reach` of the sampled system `sys.discretize Δt`,
with `inputSolution Δt η U` as every step's input set. It loses ground in two places, each with
its own accumulated zonotope: the reductions, which `LinearSysDT.reachError` already accumulates,
and the input enclosures, each wider than what one held input contributes, which
`reachInputError` accumulates the same way. `reachError` is their sum. Both summands are
zonotopes, so this is one too, and `minkDiffRep` can take it off the run (`reachInnerRep`).

## Inputs
* `sys` – linear system
* `Δt` – sampling step
* `η` – Taylor order
* `o` – zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – number of steps

## Hypotheses
* `ho` – zonotope order positive

## Output
* accumulated reduction and input enclosure errors of the sampled run
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


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
