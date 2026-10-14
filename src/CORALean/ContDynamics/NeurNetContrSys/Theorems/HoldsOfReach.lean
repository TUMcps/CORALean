module

public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachOuter
public import CORALean.Specification.Theorems.HoldsOfOuter

@[expose] public section

/-!
# A specification checked on the sampled loop's reachable set holds along it

`reach_outer` handed to `Specification.holds_of_outer`, exactly as the
discrete loop and the hybrid automaton do it. Two rates, a held input and a
network changed nothing about this step, which only ever sees a superset.

At the period boundaries, since that is where `reach` has anything to say. A
requirement between them needs the time-interval enclosure that `Operations`
records as missing.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
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
variable {ContSet : Type} [CORALean.ContSet ContSet (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSys.holds_of_reach (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) (o η N : ℕ)
    (ho : 0 < o) {Δt : ℝ} (hΔt : 0 < Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    {R₀ : S n} {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {W : S 0} {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ 0}
    (traj : sys.Trajectory π ((N : ℝ) * Δt) H R₀ W x w)
    (spec : Specification ContSet) (i : ℕ) (hi : i ≤ H)
    (h : spec.Holds (construct (sys.reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩))) :
    spec.Holds {x ((i : ℝ) * ((N : ℝ) * Δt))} :=
  spec.holds_of_outer
    (Set.singleton_subset_iff.mpr (sys.reach_outer o η N ho hΔt hε hπ traj i hi)) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
