module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterWindows
public import CORALean.Specification.Theorems.CheckSound
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A passed check on `reach` holds at every time of `[0, tFinal]`

`check_sound` on the windows of the recursive `reach`, then `reach_outer` carried
back by `holds_of_outer`. A `true` is the specification on every state the
homogeneous flow reaches from `X₀` by `tFinal`, at an order admissible for `Δt`.
`holds_of_check_wrappingFree` is the same at `reachWrappingFree`; `Reach.holds_of_check`
reaches this one at `LinearSys`, `reachInstance` now running the same recursive `reach`.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – step options
* `spec` – specification

## Hypotheses
* `htFinal` – horizon positive
* `hΔt` – step length positive
* `hη` – order at least two
* `hε` – scaled norm small enough for the Taylor order

## Conclusion
* a passed check on the computed reach implies the specification holds on the exact reach
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet ContSetLike Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {ContSet₂ : ℕ → Type} [∀ n, ContSetLike (ContSet₂ n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet₂ n) (Vec ℝ n)] [∀ n, LinComb (ContSet₂ n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) ContSet₂] [Mtimes ℐ ContSet₂]
variable {ContSet₁ : Type} [ContSetLike ContSet₁ (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.holds_of_check [Contains ContSet₁ (SetUnion (ContSet₂ n))]
    [IsDisjoint ContSet₁ (SetUnion (ContSet₂ n))] (sys : LinearSys 𝕋 n)
    {params : Reach.Params (ContSet₂ n) ℝ}
    {options : LinearSys.ReachOptions ℝ} (htFinal : 0 < params.tFinal - params.tStart)
    (hΔt : 0 < options.Δt) (hη : 2 ≤ options.η)
    (hε : ‖options.Δt • toRealMat sys.A‖ / ((options.η : ℝ) + 2) < 1)
    (spec : Specification ContSet₁) :
    spec.check (sys.reach params options) →
    (spec.Holds (sys.reachExact (params.tFinal - params.tStart) (toSet params.X₀))) :=
  fun h => spec.holds_of_outer (sys.reach_outer (sub_pos.mp htFinal) hΔt hη hε)
    (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
