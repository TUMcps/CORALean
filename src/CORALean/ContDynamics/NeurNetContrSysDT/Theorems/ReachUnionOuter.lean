import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.ReachUnionExact
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.ReachUnion
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.TrajectoryIterate
import CORALean.NN.Theorems.SoundEval

/-!
# `reachUnion` encloses `reachUnionExact`

`trajectory_iterate` at the controller's own `eval` is a `Trajectory`,
`sound_eval` needing no hypothesis; `reach_outer` places it in `reach`'s
step, and every step lands in its own branch of the `SetUnion`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reachUnion_outer (sys : NeurNetContrSysDT 𝕋 S n)
    (p : NeurNetContrSysDT.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  intro y hy
  obtain ⟨k, hk, x₀, hx₀, rfl⟩ := Set.mem_iUnion₂.mp hy
  refine SetUnion.mem_construct.mpr ⟨sys.reach ⟨X₀, 0, k⟩ ⟨p.o, p.ho⟩, ?_,
    sys.reach_outer p.ho X₀ sys.contr.sound_eval (sys.trajectory_iterate _ hx₀) k⟩
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hk))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
