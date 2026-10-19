module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.NN.Theorems.EnclosesEval

@[expose] public section

/-!
# `reachUnion` encloses `reachUnionExact`

A `reachUnionExact` witness's fields are `NeurNetContrSys.IsTrajectory`'s own, run at
the controller's own `eval`, the period `N · Δt`; `reach_outer`, at an order
admissible by `reachOrder_admissible` and the raise, and `sound_eval` place it in
`reach`'s period, landing in its own branch of the `SetUnion`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
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
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every closed-loop run over `tFinal - tStart` periods of length `N · Δt` from
`R0` is inside `reachUnion` at every period boundary. -/
theorem NeurNetContrSys.reachUnion_outer (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (U_ext : S sys.nExt) (params : Reach.Params (S n) ℕ) {options : NeurNetContrSys.ReachOptions ℝ}
    (hdt : sys.dt = (options.N : ℝ) * options.Δt) (hΔt : 0 < options.Δt) : -- --- STMT ---
    sys.reachUnionExact (params.tFinal - params.tStart)
      (construct U_ext) {0} (construct params.X₀) ⊆
      construct (sys.reachUnion U_ext params options) := by -- --- PROOF ---
  intro y hy
  obtain ⟨i, hi, x, v, w, hx0, hflow, rfl⟩ := Set.mem_iUnion₂.mp hy
  -- the disturbance is `0`, which `E` sends to `0`
  have traj : sys.IsTrajectory sys.contr.eval.out
      (params.tFinal - params.tStart) params.X₀ (construct U_ext) {0} x v w := ⟨hx0, hflow⟩
  -- the order `reachUnion` runs at clears the step, as `reachOrder`'s own does
  have hε : ‖options.Δt • sys.augment.A‖
      / (((max options.η (sys.reachOrder options.Δt) : ℕ) : ℝ) + 2) < 1 := by
    have hle : (sys.reachOrder options.Δt : ℝ)
        ≤ ((max options.η (sys.reachOrder options.Δt) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) (sys.reachOrder_admissible options.Δt)
  refine SetUnion.mem_construct_range (Nat.lt_succ_of_le hi) ?_
  exact sys.reach_outer U_ext options.ρ _ options.N options.hZonotopeOrder hΔt hdt hε
    sys.contr.encloses_eval
      (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero]) traj i hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
