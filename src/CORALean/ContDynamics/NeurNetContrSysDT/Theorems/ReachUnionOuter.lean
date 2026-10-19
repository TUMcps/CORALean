module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.IsTrajectoryOfMap
public import CORALean.ContSet.SetUnion.Theorems.Basic
public import CORALean.NN.Theorems.EnclosesEval

@[expose] public section

/-!
# `reachUnion` encloses `reachUnionExact`

`isTrajectory_of_map` at the controller's own `eval` is a `IsTrajectory`,
`sound_eval` needing no hypothesis; `reach_outer` places it in `reach`'s
step, and every step lands in its own branch of the `SetUnion`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reachUnion_outer (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) (params : Reach.Params (S n) ℕ)
    (options : NeurNetContrSysDT.ReachOptions) : -- --- CONCL ---
    sys.reachUnionExact (params.tFinal - params.tStart) (construct U_ext) (construct params.X₀)
      ⊆ construct (sys.reachUnion U_ext params options) := by -- --- PROOF ---
  intro y hy
  obtain ⟨k, hk, x, v, hx₀, hv, hstep, rfl⟩ := Set.mem_iUnion₂.mp hy
  exact SetUnion.mem_construct_range (Nat.lt_succ_of_le hk)
    (sys.reach_outer U_ext options.hZonotopeOrder params.X₀ sys.contr.encloses_eval
      (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero])
      (sys.isTrajectory_of_map (Set.mem_singleton 0) hx₀ hv hstep) k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
