module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachErrorReduced

@[expose] public section

/-!
# An inner approximation whose subtrahend has a bounded description

`reachInner` with `reachErrorReduced` in place of `reachError`. Same guarantee —
`reachInnerReduced_inner` puts it inside `reachSetExact` — and a weaker one in content:
`reachInnerReduced_subset_reachInner` says this is the smaller set, because reducing the error can
only grow what is taken off. What is bought is cost: `reachError` holds `k * n` generators, so past
`k = o` the subtrahend of `reachInner` grows without bound; `reachErrorReduced_h_le` holds this one
at `o * n`. A `Set` and not a representation, as `reachInner` is: `minkowskiDiff` is a
specification and computes nothing. `minkDiffRep` would take a reduced error as readily, and needs
a generator representation `M` from the caller.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Output
* the computed run minus its reduced error, a smaller inner approximation
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The computed run minus its reduced error: an inner approximation of
`reachSetExact` that is smaller than `reachInner`, and whose subtrahend is held at
`o * n` generators rather than growing a box per step. -/
noncomputable def LinearSysDT.reachInnerReduced (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
    (sys.reachErrorReduced ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
