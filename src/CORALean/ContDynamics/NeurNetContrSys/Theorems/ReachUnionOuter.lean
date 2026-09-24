import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachUnionExact
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachUnion
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
import CORALean.NN.Theorems.SoundEval

/-!
# `reachUnion` encloses `reachUnionExact`

A `reachUnionExact` witness's fields are `NeurNetContrSys.Trajectory`'s own,
run at the controller's own `eval`; `reach_outer` at `reachOrder_admissible`
and `sound_eval` places it in `reach`'s period, landing in its own branch of
the `SetUnion`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.reachUnion_outer (sys : NeurNetContrSys 𝕋 S n)
    (p : NeurNetContrSys.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  intro y hy
  obtain ⟨i, hi, x, hx0, hflow, rfl⟩ := Set.mem_iUnion₂.mp hy
  have traj : sys.Trajectory sys.contr.eval.out ((p.N : ℝ) * p.Δt) p.H X₀ x := ⟨hx0, hflow⟩
  refine SetUnion.mem_construct.mpr ⟨sys.reach p.o (sys.reachOrder p.Δt) p.N p.ho p.Δt X₀ i, ?_,
    sys.reach_outer p.o (sys.reachOrder p.Δt) p.N p.ho p.hΔt (sys.reachOrder_admissible p.Δt)
      sys.contr.sound_eval traj i hi⟩
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le hi))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
