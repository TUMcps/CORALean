import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
import CORALean.Specification.Theorems.HoldsOfOuter

/-!
# A specification checked on the sampled loop's reachable set holds along it

`reach_outer` handed to `Specification.holds_of_outer`, exactly as the
discrete loop and the hybrid automaton do it. Two rates, a held input and a
network changed nothing about this step, which only ever sees a superset.

At the period boundaries, since that is where `reach` has anything to say. A
requirement between them needs the time-interval enclosure that `Operations`
records as missing.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]

theorem NeurNetContrSys.holds_of_reach (sys : NeurNetContrSys 𝕋 S n) (o η N : ℕ) {Δt : ℝ}
    (hΔt : 0 < Δt) (hε : ‖Δt • toRealMat sys.plant.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    {R₀ : S n} {x : ℝ → Vec ℝ n} (traj : sys.Trajectory ((N : ℝ) * Δt) H R₀ x)
    (spec : Specification (Vec ℝ n)) (i : ℕ) (hi : i ≤ H)
    (h : spec.Holds (construct (sys.reach o η N Δt R₀ i))) :
    spec.Holds {x ((i : ℝ) * ((N : ℝ) * Δt))} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.reach_outer o η N hΔt hε traj i hi)) h

end CORALean.Real
