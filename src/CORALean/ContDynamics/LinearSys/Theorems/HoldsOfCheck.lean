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
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.holds_of_check [Contains ContSet (SetUnion (S n))]
    [IsDisjoint ContSet (SetUnion (S n))] (sys : LinearSys 𝕋 n) {params : Reach.Params (S n) ℝ}
    {options : LinearSys.ReachStepOptions ℝ} (htFinal : 0 < params.tFinal - params.tStart)
    (hΔt : 0 < options.Δt) (hη : 2 ≤ options.η)
    (hε : ‖options.Δt • toRealMat sys.A‖ / ((options.η : ℝ) + 2) < 1)
    (spec : Specification ContSet) :
    spec.check (sys.reach params options) →
    (spec.Holds (sys.reachExact (params.tFinal - params.tStart) (construct params.X₀))) :=
  fun h => spec.holds_of_outer (sys.reach_outer htFinal hΔt hη hε) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
