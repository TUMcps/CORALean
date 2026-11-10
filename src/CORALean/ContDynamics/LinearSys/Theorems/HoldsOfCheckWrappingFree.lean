module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachWrappingFreeOuter
public import CORALean.Specification.Theorems.CheckSound
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A passed check on `reachWrappingFree` holds at every time of `[0, tFinal]`

The same shape as `Reach.holds_of_check`, but at `reachWrappingFree` and `reachExact`
directly rather than through the (now recursive) `LinearSys` instance of `Reach`:
`check_sound` on the windows, then `reachWrappingFree_outer` carried back by
`holds_of_outer`. A `true` is the specification on every state the homogeneous flow
reaches from `X₀` by `tFinal`, at any `η`; `holds_of_check` is the same at the recursive
`reach`, which `LinearSys.reachInstance` runs.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – step options
* `spec` – specification

## Hypotheses
* `hΔt` – step length positive

## Conclusion
* a passed check on the wrapping-free reach implies the specification holds on the exact reach
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet₂ n) (Vec ℝ n)] [∀ n, LinComb (ContSet₂ n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) ContSet₂] [Mtimes ℐ ContSet₂]
variable {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.holds_of_check_wrappingFree [Contains ContSet₁ (SetUnion (ContSet₂ n))]
    [IsDisjoint ContSet₁ (SetUnion (ContSet₂ n))] (sys : LinearSys 𝕋 n)
    (params : Reach.Params (ContSet₂ n) ℝ)
    {options : LinearSys.ReachOptions ℝ} (hΔt : 0 < options.Δt)
    (spec : Specification ContSet₁) :
    spec.check (sys.reachWrappingFree params options) →
    (spec.Holds (sys.reachExact (params.tFinal - params.tStart) (toSet params.X₀))) :=
  fun h => spec.holds_of_outer (sys.reachWrappingFree_outer params hΔt) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
