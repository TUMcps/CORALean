import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnion
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
import CORALean.NN.Theorems.SoundEval

/-!
# `reachUnion` encloses `reachUnionExact`

A `reachUnionExact` witness's fields are `NeurNetContrSys.Trajectory`'s own, run at
the controller's own `eval`, the period `N · Δt`; `reach_outer`, at an order
admissible by `reachOrder_admissible` and the raise, and `sound_eval` place it in
`reach`'s period, landing in its own branch of the `SetUnion`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet Plus Reduce Mtimes Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every closed-loop run over `tFinal - tStart` periods of length `N · Δt` from
`R0` is inside `reachUnion` at every period boundary. -/
theorem NeurNetContrSys.reachUnion_outer (sys : NeurNetContrSys 𝕋 S n)
    (params : Reach.Params (S n) ℕ) {options : NeurNetContrSys.ReachOptions ℝ}
    (hΔt : 0 < options.Δt) :
    sys.reachUnionExact ((options.N : ℝ) * options.Δt) (params.tFinal - params.tStart)
      (construct params.X₀) ⊆ construct (sys.reachUnion params options) := by -- --- PROOF ---
  intro y hy
  obtain ⟨i, hi, x, hx0, hflow, rfl⟩ := Set.mem_iUnion₂.mp hy
  have traj : sys.Trajectory sys.contr.eval.out ((options.N : ℝ) * options.Δt)
      (params.tFinal - params.tStart) params.X₀ x := ⟨hx0, hflow⟩
  -- the order `reachUnion` runs at clears the step, as `reachOrder`'s own does
  have hε : ‖options.Δt • toRealMat sys.plant.A‖
      / (((max options.η (sys.reachOrder options.Δt) : ℕ) : ℝ) + 2) < 1 := by
    have hle : (sys.reachOrder options.Δt : ℝ)
        ≤ ((max options.η (sys.reachOrder options.Δt) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) (sys.reachOrder_admissible options.Δt)
  refine SetUnion.mem_construct.mpr
    ⟨_, List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hi)), ?_⟩
  exact sys.reach_outer options.ρ _ options.N options.hZonotopeOrder hΔt hε
    sys.contr.sound_eval traj i hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
