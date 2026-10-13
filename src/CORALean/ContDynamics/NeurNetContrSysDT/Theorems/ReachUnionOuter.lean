module

public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.ReachUnion
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryIterate
public import CORALean.NN.Theorems.SoundEval

@[expose] public section

/-!
# `reachUnion` encloses `reachUnionExact`

`trajectory_iterate` at the controller's own `eval` is a `Trajectory`,
`sound_eval` needing no hypothesis; `reach_outer` places it in `reach`'s
step, and every step lands in its own branch of the `SetUnion`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reachUnion_outer (sys : NeurNetContrSysDT 𝕋 S n)
    (params : Reach.Params (S n) ℕ) (options : NeurNetContrSysDT.ReachOptions) :
    sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
      ⊆ construct (sys.reachUnion params options) := by -- --- PROOF ---
  intro y hy
  obtain ⟨k, hk, x₀, hx₀, rfl⟩ := Set.mem_iUnion₂.mp hy
  refine SetUnion.mem_construct.mpr ⟨sys.reach ⟨params.X₀, 0, k⟩ options, ?_,
    sys.reach_outer options.hZonotopeOrder params.X₀ sys.contr.sound_eval
      (sys.trajectory_iterate _ hx₀) k⟩
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hk))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
