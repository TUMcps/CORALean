module

public import CORALean.ContDynamics.LinearSysDT.Operations.ReachError

@[expose] public section

/-!
# An inner approximation of a reachable set

`reachInner` is the computed run minus the error that run accumulated: `reachInner_inner` puts it
*inside* `reachSetExact`, the opposite direction to every other reachability guarantee here, where
the computed set is the larger one. `reachInner` is a `Set` — `minkowskiDiff` is a specification
and computes nothing — so on its own it is a guarantee about a set rather than an object a later
step could consume; `reachInnerRep` in `Operations/` is the same difference at a representation.
`minkDiffAligned` cannot take that place: it asks for equal generator counts and for every error
generator to be a scaled copy of the run generator at the same index, which earlier boxes carried
through `A` are not.

## Inputs
* `sys` – system
* `o` – maximum zonotope order
* `R₀` – initial zonotope
* `U` – input zonotope
* `k` – step

## Hypotheses
* `ho` – order positive

## Output
* the computed run minus its accumulated error, an inner approximation
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

/-- The computed run minus its own accumulated error — an inner approximation
of `reachSetExact`, as a set. -/
noncomputable def LinearSysDT.reachInner (sys : LinearSysDT ℝ n) (o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec ℝ n)) (k : ℕ) : Set (Vec ℝ n) :=
  minkowskiDiff (sys.reach (S := 𝒵) ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct
    (sys.reachError ⟨R₀, U, 0, k⟩ ⟨o, ho⟩).construct

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
