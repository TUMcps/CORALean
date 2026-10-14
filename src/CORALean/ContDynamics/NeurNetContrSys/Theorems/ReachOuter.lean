module

public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizonInputSolution
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.CartProdOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ExtendedFEqAugment
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ProjectOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithTimePointOuter
public import CORALean.ContSet.ContSet.Definitions.CompactSet
public import CORALean.ContSet.ContSet.Theorems.Basic
public import CORALean.ContSet.ContSet.Definitions.ConvexSet

@[expose] public section

/-!
# `NeurNetContrSys.reach` contains every sampled run at the period boundaries

[1, Alg. 2] at a linear plant: `reachWith_timePoint_outer` at the plant's own reachability. A
control period is a run of the extended system (`Trajectory.period`), at a linear plant one of
the augmented system `[A B; 0 0]`, `[c; 0]` under the constant input `[c; 0]`
(`extended_f_eq_augment`), handed to `reach_outer_horizon_inputSolution` for `N` steps;
`cartProd_outer` and `project_outer` are the product and the projection. The horizon is exactly
the period, `Set.Icc 0 (N Δt)`, and the order is admissible for the augmented matrix. Period
boundaries only: between them `reach` says nothing, and the network is not invoked either.

Stated at a convex, compact representation, which is what makes `inputSolution`'s six topological
hypotheses instances rather than arguments; `reachSet_subset_reach` restates it on the reachable
set.

## References

* [1] N. Kochdumper et al. "Open- and Closed-Loop Neural Network Verification
      using Polynomial Zonotopes". arXiv:2207.02715, 2022.
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is inside `reach` at every period boundary.
`Δt` is the reachability step, `N Δt` the control period, and the two are related only here. -/
theorem NeurNetContrSys.reach_outer (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) (o η N : ℕ)
    (ho : 0 < o) {Δt : ℝ} (hΔt : 0 < Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1)
    {H : ℕ} {R₀ : S n} {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π) {W : S 0}
    {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ 0} (traj : sys.Trajectory π ((N : ℝ) * Δt) H R₀ W x w) :
    ∀ i ≤ H,
      x ((i : ℝ) * ((N : ℝ) * Δt)) ∈
        construct (sys.reach ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by -- --- PROOF ---
  have hNΔ : (0:ℝ) ≤ (N : ℝ) * Δt := mul_nonneg (Nat.cast_nonneg N) hΔt.le
  refine sys.reachWith_timePoint_outer _ _ _
    (fun X Y _ _ hx hu => NeurNetContrSys.cartProd_outer X Y hx hu)
    (fun Z _ hz => NeurNetContrSys.project_outer Z hz) ?_ hπ traj
  -- a period of the extended system is a run of the augmented linear one, `N` steps of `Δt`
  intro Z z w' hz
  have hc : sys.augment.CanonicalClassicalTrajectory (Set.Icc 0 ((N : ℝ) * Δt)) Z
      (OfPoint.ofPoint sys.augment.c) z (fun _ => sys.augment.c) :=
    ⟨hz.init, fun _ _ => OfPoint.mem_ofPoint _, fun t ht => by
      have h := hz.flow t ht
      rw [sys.extended_f_eq_augment] at h
      exact h⟩
  have key := (hc.trajectory (convex_Icc 0 _) ⟨le_rfl, hNΔ⟩
    (CompactSet.isBounded_construct _)).reach_outer_horizon_inputSolution
    (K := N) hΔt subset_rfl η hε
    (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
    (CompactSet.isBounded_construct _) (ConvexSet.convex_construct _)
    (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _) ho N le_rfl
  exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
