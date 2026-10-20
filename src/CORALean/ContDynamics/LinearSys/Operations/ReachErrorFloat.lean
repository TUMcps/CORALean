module

public import CORALean.ContDynamics.LinearSys.Operations.ReachExcessFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachInputErrorFloat

@[expose] public section

/-!
# What a float sampled run owes, as a float zonotope

The float counterpart of `reachError`. The run is `discretizeEnclosureFloat`'s `reach` with
`inputSolutionFloat Δt η U` as its input set, and what it owes is measured against the exact
held-input sampled set: `discretize Δt` from `R₀`'s nominal zonotope under `(∫₀^Δt e^{As} ds) U`
at `U`'s. Two summands, as `reachError` has: the run's own excess `reachExcessFloat`, and the
input enclosures' error boxes `reachInputErrorFloat`. A different quantity from `reachError`: it
also pays every rounding of the float run and the width of `[e^{AΔt}]`, because the inner
approximation it serves takes it off the float run. Each part is an outer enclosure computed in
`𝕋`, so it only errs large; `discretizeEnclosureFloat_reach_subset_add_errorFloat` is the guarantee.

## Inputs
* `sys` – linear system
* `Δt` – float sampling step
* `η` – Taylor order
* `o` – zonotope order
* `R₀` – initial float zonotope
* `U` – input float zonotope
* `k` – number of steps

## Hypotheses
* `ho` – zonotope order positive

## Output
* float zonotope of the run's excess and the input enclosures' error boxes
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `k` float sampled steps owe against the exact held-input sampled set: the run's own
excess and the input enclosures' error boxes. -/
def LinearSys.reachErrorFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η o : ℕ) (ho : 0 < o)
    (R₀ U : Zonotope (Vec 𝕋 n)) (k : ℕ) : Zonotope (Vec 𝕋 n) :=
  sys.reachExcessFloat Δt η o ho R₀ U k ⊞ sys.reachInputErrorFloat Δt η U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
