import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachSet
import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter

/-!
# `reach` encloses the reachable set at the period boundaries

`reach_outer` restated on `reachSet`: what it says of every run at `iΔtc`, this
says of the set of them at once, so a specification about the reachable set
meets the loop's enclosure as a single inclusion.

Period boundaries only, and for the reason `ReachOuter` already gives: between
them `reachSet` says nothing and the network is not invoked either, so the two
silences coincide. Unlike `LinearSys.reachSet`, whose flow gets a stated
time-interval enclosure between sample points, there is no such statement to
restate here — the gap sits in what the class proves, not only in this file.

[1, Alg. 2]'s postcondition, `R ⊇ R([0, tF])`, read at one control cycle.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   30-September-2026
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
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Reach for this at the period boundaries; the guarantee attaches to the
reachable set, not to a run of it. -/
theorem NeurNetContrSys.reachSet_subset_reach (sys : NeurNetContrSys 𝕋 S n) (o η N : ℕ)
    (ho : 0 < o) {Δt : ℝ} (hΔt : 0 < Δt)
    (hε : ‖Δt • toRealMat sys.plant.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ} (R₀ : S n)
    {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π) {i : ℕ} (hi : i ≤ H) :
    sys.reachSet π ((N : ℝ) * Δt) H R₀ ((i : ℝ) * ((N : ℝ) * Δt))
      ⊆ construct (sys.reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by
  rintro _ ⟨x, traj, rfl⟩
  exact sys.reach_outer o η N ho hΔt hε hπ traj i hi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
