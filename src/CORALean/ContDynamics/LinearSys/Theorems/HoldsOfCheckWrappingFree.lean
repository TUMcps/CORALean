import CORALean.ContDynamics.LinearSys.Theorems.ReachWrappingFreeOuter
import CORALean.Specification.Theorems.CheckSound
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A passed check on `reachWrappingFree` holds at every time of `[0, tFinal]`

The same shape as `Reach.holds_of_check`, but at `reachWrappingFree` and `reachExact`
directly rather than through `Params` and the (now recursive) `LinearSys` instance:
`check_sound` on the windows, then `reachWrappingFree_outer` carried back by
`holds_of_outer`. A `true` is the specification on every state the homogeneous flow
reaches from `X₀` by `tFinal`, at any `η`; `holds_of_check` is the same at the recursive
`reach`, which `LinearSys.reachInstance` runs.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   27-September-2026
-- Last revision: ---


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
    [IsDisjoint ContSet (SetUnion (S n))] (sys : LinearSys 𝕋 n) {tFinal Δt : ℝ} (hΔt : 0 < Δt)
    (η : ℕ) (X₀ : S n) (spec : Specification ContSet) :
    spec.check (sys.reachWrappingFree tFinal Δt η X₀) →
    (spec.Holds (sys.reachExact tFinal (construct X₀))) :=
  fun h => spec.holds_of_outer (sys.reachWrappingFree_outer hΔt X₀) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
