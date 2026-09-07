import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizonInputSolution
import CORALean.ContDynamics.NeurNetContrSys.Operations
import CORALean.ContDynamics.NeurNetContrSys.Theorems.Period
import CORALean.ContSet.ContSet.CompactSet
import CORALean.ContSet.ContSet.ConvexSet

/-!
# `NeurNetContrSys.reach` contains every sampled run at the period boundaries

An induction on the control period, whose step is `Trajectory.period` — the run's own period read as
a linear run under the enclosed input set — handed to `reach_outer_horizon_inputSolution` for `N`
steps; both halves were written without the other in view, and this file only lines the clocks up.

The horizon is exactly the period, `Set.Icc 0 (N Δt)` both times, so nothing is
assumed about the run beyond the periods the trajectory speaks about. That is
what makes the chain a chain: period `i` is sound on its own window, and the
enclosure it ends at is the next period's initial set.

Period boundaries only. Between them `reach` says nothing and the network is
not invoked either, so the two silences coincide — unlike `relinReach`, whose
dynamics keep running between steps and get a stated time-interval enclosure.

Stated at a convex, compact representation, which is what makes `inputSolution`'s six topological
hypotheses instances rather than arguments. Reach for `reachSet_subset_reach` for the same guarantee
restated on the reachable set rather than on one run.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


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

/-- Every zero-order-hold run of `H` control periods is inside `reach` at every
period boundary. `Δt` is the reachability step, `N Δt` the control period, and
the two are related only here. -/
theorem NeurNetContrSys.reach_outer (sys : NeurNetContrSys 𝕋 S n) (o η N : ℕ) (ho : 0 < o)
    {Δt : ℝ} (hΔt : 0 < Δt) (hε : ‖Δt • toRealMat sys.plant.A‖ / ((η : ℝ) + 2) < 1) {H : ℕ}
    {R₀ : S n} {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x : ℝ → Vec ℝ n} (traj : sys.Trajectory π ((N : ℝ) * Δt) H R₀ x) :
    ∀ i ≤ H,
      x ((i : ℝ) * ((N : ℝ) * Δt)) ∈ construct (sys.reach o η N ho Δt R₀ i) := by -- --- PROOF ---
  intro i
  -- the induction is on the control period, `traj.period` being its step
  induction i with
  | zero =>
    intro _
    show x (((0 : ℕ) : ℝ) * ((N : ℝ) * Δt)) ∈ construct R₀
    simpa using traj.init
  | succ i ih =>
    intro hi
    have hiH : i < H := Nat.lt_of_succ_le hi
    have key := (traj.period hπ i hiH _ (ih hiH.le)).reach_outer_horizon_inputSolution
      (K := N) hΔt subset_rfl η hε
      (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
      (CompactSet.isBounded_construct _) (ConvexSet.convex_construct _)
      (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _) ho N le_rfl
    -- the conclusion unfolded, so `key` matches it at the period's own clock
    show x (((i + 1 : ℕ) : ℝ) * ((N : ℝ) * Δt)) ∈ construct
      ((sys.plant.discretize Δt).reach o ho (sys.reach o η N ho Δt R₀ i)
        (sys.plant.inputSolution Δt η
          (sys.contr.enclose (sys.reach o η N ho Δt R₀ i))) N)
    rw [show ((i + 1 : ℕ) : ℝ) * ((N : ℝ) * Δt)
      = (i : ℝ) * ((N : ℝ) * Δt) + (N : ℝ) * Δt from by push_cast; ring]
    exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
