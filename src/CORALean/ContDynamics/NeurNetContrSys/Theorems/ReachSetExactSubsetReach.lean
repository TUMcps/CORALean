module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSetExact
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter

@[expose] public section

/-!
# `reach` encloses the reachable set at the period boundaries

`reach_outer` restated on `reachSetExact`: what it says of every run at `iΔtc`, this
says of the set of them at once, so a specification about the reachable set
meets the loop's enclosure as a single inclusion.

Period boundaries only, and for the reason `ReachOuter` already gives: between
them `reachSetExact` says nothing and the network is not invoked either, so the two
silences coincide. Unlike `LinearSys.reachSetExact`, whose flow gets a stated
time-interval enclosure between sample points, there is no such statement to
restate here — the gap sits in what the class proves, not only in this file.

[1, Alg. 2]'s postcondition, `R ⊇ R([0, tF])`, read at one control cycle.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this at the period boundaries; the guarantee attaches to the
reachable set, not to a run of it. -/
theorem NeurNetContrSys.reachSetExact_subset_reach (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (U_ext : S sys.nExt)
    (o η N : ℕ) (ho : 0 < o) {Δt : ℝ} (hΔt : 0 < Δt) (hdt : sys.dt = (N : ℝ) * Δt)
    (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ} (R₀ : S n)
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π) (W : Set (Vec ℝ sys.plant.r))
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {i : ℕ} (hi : i ≤ H) : -- --- STMT ---
    sys.reachSetExact π H R₀ (construct U_ext) W ((i : ℝ) * sys.dt)
      ⊆ construct (sys.reach U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by -- --- PROOF ---
  rintro _ ⟨x, v, w, traj, rfl⟩
  exact sys.reach_outer U_ext o η N ho hΔt hdt hε hπ hW traj i hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
