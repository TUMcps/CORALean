module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachOuterHorizonInputSolution
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.CartProdOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.AugmentFlow
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ProjectOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithTimePointOuter
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `NeurNetContrSys.reach` contains every sampled run at the period boundaries

[1, Alg. 2] at a linear plant: `reachWith_timePoint_outer` at the plant's own reachability. A
control period is a run of the plant under the held input (`IsTrajectory.flow`), at a linear plant
whose disturbance `E` sends to `0` one of the augmented system under the constant input
(`augment_flow`), handed to `reach_outer_horizon_inputSolution` for `N` steps; `cartProd_outer` and
`project_outer` are the product and the projection. The horizon is exactly the period,
`Set.Icc 0 (N Δt)`, and the order is admissible for the augmented matrix. Period boundaries only:
between them `reach` says nothing. Stated at a convex, compact representation, which makes
`inputSolution`'s six topological hypotheses instances; `reachSetExact_subset_reach` restates it.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input set
* `o` – maximum zonotope order
* `η` – Taylor order
* `N` – steps per period
* `Δt` – step size
* `H` – number of periods
* `R₀` – initial set
* `π` – controller function
* `W` – disturbance set
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `ho` – order positive
* `hΔt` – step positive
* `hdt` – the period is `N` steps
* `hε` – order admissible
* `hπ` – the network encloses `π`
* `hW` – disturbances sent to zero by the disturbance matrix
* `traj` – closed-loop trajectory

## Conclusion
* the state at every period boundary lies in the reachable set

## References

* [1] N. Kochdumper, C. Schilling, M. Althoff and S. Bak. "Open- and Closed-Loop Neural Network
      Verification using Polynomial Zonotopes". arXiv preprint arXiv:2207.02715, 2022.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
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

/-- Every zero-order-hold run of `H` control periods, under external inputs in `U_ext` and a
disturbance `E` sends to `0`, is inside `reach` at every period boundary.
`Δt` is the reachability step, `N Δt = sys.dt` the control period, related only here. -/
theorem NeurNetContrSys.reach_outer (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (U_ext : S sys.nExt) (o η N : ℕ) (ho : 0 < o) {Δt : ℝ} (hΔt : 0 < Δt)
    (hdt : sys.dt = (N : ℝ) * Δt) (hε : ‖Δt • sys.augment.A‖ / ((η : ℝ) + 2) < 1)
    {H : ℕ} {R₀ : S n} {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π)
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.IsTrajectory π H R₀ (construct U_ext) W x v w) : -- --- CONCL ---
    ∀ i ≤ H,
      x ((i : ℝ) * sys.dt) ∈
        construct (sys.reach U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by -- --- PROOF ---
  refine sys.reachWith_timePoint_outer _ _ _
    (fun X Y _ _ hx hu => NeurNetContrSys.cartProd_outer X Y hx hu)
    (fun Z _ hz => NeurNetContrSys.project_outer Z hz) ?_ hπ traj
  -- a period of the plant is a run of the augmented linear system, `N` steps of `Δt`
  intro Z z u v' w' hz hzt
  obtain ⟨hcont, hvU, hmeas, hflow⟩ :=
    sys.augment_flow (CompactSet.isBounded_construct U_ext) hW hzt
  have hc : sys.augment.IsCanonicalTrajectory (Set.Icc 0 sys.dt) Z
      (Plus.plus (Mtimes.mtimes (𝕄 := Mat ℝ) sys.augment.B U_ext) (OfPoint.ofPoint sys.augment.c))
      (fun t => Fin.append (z t) u) (fun t => sys.augment.B *ᵥ v' t + sys.augment.c) :=
    ⟨hz, fun t ht => Plus.plus_outer _ _ (Set.add_mem_add (Mtimes.mtimes_outer _ _ (by
        simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
        exact Set.mem_image_of_mem _ (hvU t ht))) (OfPoint.mem_ofPoint _)), hmeas, hcont, hflow⟩
  have key := hc.reach_outer_horizon_inputSolution
    (K := N) hΔt (Set.Icc_subset_Icc_right hdt.ge) η hε
    (ConvexSet.convex_construct _) (CompactSet.isClosed_construct _)
    (CompactSet.isBounded_construct _) (ConvexSet.convex_construct _)
    (CompactSet.isClosed_construct _) (CompactSet.isBounded_construct _) ho N le_rfl
  rw [hdt]
  exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
