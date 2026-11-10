module

public import CORALean.ContDynamics.LinearSys.Operations.ReachAdmissible
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterWindows

@[expose] public section

/-!
# `reachAdmissible` encloses `reachExact`, at any `η`

`reach_outer`'s own statement, at the order `reachAdmissible` raises to, so its
caller supplies no `hη` and no `hε`: `reachOrder_admissible` gives `hε`
directly at that raised order, and `2 ≤ max η (reachOrder Δt + 2)` is
immediate. `LinearSys.reachInstance` states its guarantee through this.

## Inputs
* `sys` – linear system
* `params` – reach parameters
* `options` – step options

## Hypotheses
* `htFinal` – horizon positive
* `hΔt` – step length positive

## Conclusion
* the exact reach lies in the admissible-order reach
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
variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)]
variable [∀ n, Plus (ContSet n) (Vec ℝ n)] [∀ n, LinComb (ContSet n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) ContSet] [Mtimes ℐ ContSet]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every `t ∈ [0, tFinal - tStart]`,
is in one of `reachAdmissible`'s windows, at any order `η`. -/
theorem LinearSys.reachAdmissible_outer (sys : LinearSys 𝕋 n)
    {params : Reach.Params (ContSet n) ℝ} {options : LinearSys.ReachOptions ℝ}
    (htFinal : 0 < params.tFinal - params.tStart) (hΔt : 0 < options.Δt) : -- --- CONCL ---
    sys.reachExact (params.tFinal - params.tStart) (toSet params.X₀)
      ⊆ toSet (sys.reachAdmissible params options) := by -- --- PROOF ---
  unfold LinearSys.reachAdmissible
  -- `reachOrder_admissible` gives `hε` at the order `reachAdmissible` runs at directly
  have hη : 2 ≤ max options.η (sys.reachOrder options.Δt + 2) :=
    le_trans (Nat.le_add_left 2 (sys.reachOrder options.Δt)) (le_max_right _ _)
  have hε := sys.reachOrder_admissible options.Δt
    (le_max_right options.η (sys.reachOrder options.Δt + 2))
  exact sys.reach_outer (options := ⟨options.Δt, _⟩) (sub_pos.mp htFinal) hΔt hη hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
