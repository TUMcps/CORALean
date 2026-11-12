module

public import CORALean.Global.TakeThrough
public import CORALean.HybridDynamics.Operations.LocationReachFloat
public import CORALean.Specification.Instances

@[expose] public section

/-!
# `Location.stayFloat`

The continuous part of CORA's `location/reach` as `hybridAutomaton/reach` runs it: `N` steps of the
location from `X₀`, `Location.reachFloat` at the horizon `N Δt`, kept up to and including the first
time-interval set that is certified disjoint from the invariant (CORA stops there, its
`'invariant'` specification). The sets are not cut to the invariant. No steps give no sets.

## Inputs
* `ℓ` – location
* `N` – number of steps
* `options` – reach options
* `X₀` – initial zonotope

## Output
* time-interval sets of the stay, none on failure
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sets `R(τ_0), …, R(τ_{j})` of the `N` steps of a stay from `X₀`, `j` the first with the
invariant certified disjoint from it. -/
def Location.stayFloat (ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) (N : ℕ)
    (options : LinearSys.ReachFloatOptions 𝕋) (X₀ : Zonotope (Vec 𝕋 n)) :
    Option (List (Zonotope (Vec 𝕋 n))) :=
  if N = 0 then some [] else do
    let Rs ← ℓ.reachFloat (N * ToRat.toRat options.Δt) options X₀   -- the N steps
    pure (takeThrough (fun R => IsDisjoint.isDisjoint ℓ.inv R) Rs) -- up to the first exit

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
