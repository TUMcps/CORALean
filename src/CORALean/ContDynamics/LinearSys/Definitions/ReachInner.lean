module

public import CORALean.ContDynamics.LinearSys.Operations.ReachError

@[expose] public section

/-!
# An inner approximation of a continuous reachable set, over a whole run

`LinearSysDT.reachInner` at the sample times of a continuous-time system: the
sampled run minus everything it owes. `reachInner_inner` puts it inside
`reachSetExact` at `t = kΔt`, the states the system's Carathéodory runs reach.

An outer approximation minus its error bound is [1]'s route to an inner one;
here the bound is a zonotope, carried along the run rather than restated.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order
* `o` – zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – number of steps

## Hypotheses
* `ho` – order is positive

## Output
* inner approximation of the reachable set at the step count's time

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
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

/-- The sampled run minus its own accumulated error — an inner approximation of
the reachable set at `t = kΔt`, as a set. -/
noncomputable def LinearSys.reachInner (sys : LinearSys 𝕋 n) (Δt : ℝ) (η o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff
    ((sys.discretize Δt).reach (S := 𝒵) ⟨R₀, sys.inputSolution (S := 𝒵) Δt η U, 0, k⟩
      ⟨o, ho⟩).construct
    (sys.reachError Δt η o ho R₀ U k).construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
