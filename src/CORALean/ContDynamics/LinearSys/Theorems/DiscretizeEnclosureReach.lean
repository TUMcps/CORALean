import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosure
import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuter

/-!
# `discretizeEnclosure`'s trajectory lands in `reach`

The whole proof is `discretizeEnclosure` handed to `LinParamSysDT.reach_outer`:
once a sampled run is a trajectory of the enclosed system, the discrete
guarantee is the continuous one at the sample times.

`Mtimes ℐ S`, not `Mtimes (Mat ℝ) S`: the system matrix now ranges over an
interval matrix, not a single real one.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] in
/-- Sampling into the enclosed system and then running its recursion; nothing
here combines, which is why `LinComb` is not asked for. -/
theorem LinearSys.Trajectory.discretizeEnclosure_mem_reach {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U Ud : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} {η : ℕ}
    (traj : sys.Trajectory T R₀ U x u) (hΔt : 0 ≤ Δt) (hT : Set.Ici 0 ⊆ T)
    (hU : Bornology.IsBounded (construct U))
    (hUd : ∀ k : ℕ, sys.stepInput u Δt k ∈ construct Ud)
    (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (o k : ℕ) :
    x (k * Δt) ∈ construct ((sys.discretizeEnclosure Δt η).reach o R₀ Ud k) :=
  (sys.discretizeEnclosure Δt η).reach_outer o R₀ Ud
    (traj.discretizeEnclosure hΔt hT hU hUd hε) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
