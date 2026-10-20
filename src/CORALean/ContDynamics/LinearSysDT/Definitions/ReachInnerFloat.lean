module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorFloat

@[expose] public section

/-!
# An inner approximation of a reachable set, from a float run

The float counterpart of `reachInner`: the computed float run minus the error that run
accumulated, put inside `reachSetExact` — the *exact*, real-valued reachable set, over the
nominal parts of `R₀` and `U` — by `reachInnerFloat_inner`. A float computation certifying
something about the true reachable set is what the two-layer design is for: `reachInnerFloat` is
`Set (Vec ℝ n)`, the same real space every layer denotes into. `minkowskiDiff` is a specification
and computes nothing, as at `reachInner`; a representation-level version would first need a real
zonotope standing for the float run's whole construct, which no operation here builds.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Output
* the computed float run minus its accumulated error, an inner approximation
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The computed float run minus its own accumulated error — an inner
approximation of the exact reachable set, as a set. -/
noncomputable def LinearSysDT.reachInnerFloat (sys : LinearSysDT 𝕋 n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.reach (S := 𝒵[𝕋]) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
    (sys.reachErrorFloat ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
