module

public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.SimulateTrajectory

@[expose] public section

/-!
# A sampled run stays inside the reachable set

`simulate_trajectory` handed to `reach_outer`: the one fact `simulate` is for,
stated once so nothing downstream redoes the induction on `reach`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.simulate_mem_reach (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n) {o : ℕ}
    (ho : 0 < o)
    (R₀ : S n) {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ construct R₀) (k : ℕ) :
    sys.simulate π x₀ k ∈ construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) :=
  sys.reach_outer ho R₀ hπ (fun v hv => by rw [Set.mem_singleton_iff.1 hv, Matrix.mulVec_zero])
    (sys.simulate_trajectory π (Set.mem_singleton 0) hx₀) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
