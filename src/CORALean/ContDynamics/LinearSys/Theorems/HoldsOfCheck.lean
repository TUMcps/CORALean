import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterWindows
import CORALean.Specification.Theorems.CheckSound
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A passed check on `reach` holds at every time of `[0, tFinal]`

`check_sound` on the windows of the recursive `reach`, then `reach_outer` carried
back by `holds_of_outer`. A `true` is the specification on every state the
homogeneous flow reaches from `X₀` by `tFinal`, at an order admissible for `Δt`.
`holds_of_check_wrappingFree` is the same at `reachWrappingFree`, which is what
`Reach.holds_of_check` reaches at `LinearSys`.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
-- Last revision: ---


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
    [IsDisjoint ContSet (SetUnion (S n))] (sys : LinearSys 𝕋 n) {tFinal Δt : ℝ}
    (htFinal : 0 < tFinal) (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n)
    (spec : Specification ContSet) :
    spec.check (sys.reach tFinal Δt (m + 2) X₀) →
    (spec.Holds (sys.reachExact tFinal (construct X₀))) :=
  fun h => spec.holds_of_outer (sys.reach_outer htFinal hΔt hε X₀) (spec.check_sound _ h)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
