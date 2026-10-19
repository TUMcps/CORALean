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
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.holds_of_check_wrappingFree [Contains ContSet (SetUnion (S n))]
    [IsDisjoint ContSet (SetUnion (S n))] (sys : LinearSys 𝕋 n) (params : Reach.Params (S n) ℝ)
    {options : LinearSys.ReachStepOptions ℝ} (hΔt : 0 < options.Δt)
    (spec : Specification ContSet) : -- --- STMT ---
    spec.check (sys.reachWrappingFree params options) →
    (spec.Holds (sys.reachExact (params.tFinal - params.tStart) (construct params.X₀))) :=
  fun h => spec.holds_of_outer (sys.reachWrappingFree_outer params hΔt) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
