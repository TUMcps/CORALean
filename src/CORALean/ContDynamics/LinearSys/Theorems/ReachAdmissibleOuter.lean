import CORALean.ContDynamics.LinearSys.Operations.ReachAdmissible
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterWindows

/-!
# `reachAdmissible` encloses `reachExact`, at any `η`

`reach_outer`'s own statement, at the order `reachAdmissible` raises to, so its
caller supplies no `m` and no `hε`: `reachOrder_admissible` gives both, the
raised order written `m + 2` by the same subtraction `reachWrappingFree_outer`
runs. `LinearSys.reachInstance` states its guarantee through this.
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every `t ∈ [0, tFinal]`,
is in one of `reachAdmissible`'s windows, at any order `η`. -/
theorem LinearSys.reachAdmissible_outer (sys : LinearSys 𝕋 n) {tFinal Δt : ℝ}
    (htFinal : 0 < tFinal) (hΔt : 0 < Δt) (η : ℕ) (X₀ : S n) : sys.reachExact tFinal (construct X₀)
      ⊆ construct (sys.reachAdmissible tFinal Δt η X₀) := by -- --- PROOF ---
  -- the order `reachAdmissible` runs at, `m + 2` in `reach_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max η (sys.reachOrder Δt + 2) = m + 2 :=
    ⟨max η (sys.reachOrder Δt + 2) - 2, by omega⟩
  have hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    sys.reachOrder_admissible Δt (hm ▸ le_max_right _ _)
  unfold LinearSys.reachAdmissible
  rw [hm]
  exact sys.reach_outer htFinal hΔt hε X₀

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
