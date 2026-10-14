module

public import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureFloatHorizon
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ExtendedFEqAugment
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachWithTimePointOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatAugmentFloat
public import CORALean.ContSet.Zonotope.Float.Theorems.CartProdExact
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint
public import CORALean.ContSet.Zonotope.Float.Theorems.ProjectOuter

@[expose] public section

/-!
# `NeurNetContrSys.reachFloat` contains every sampled run at the period boundaries

`reach_outer` in floats: `reachWith_timePoint_outer` with the float product (`cartProd_exact`)
and projection (`project_outer`), a period read as a run of the augmented system — its float
matrices reading as the real ones (`toRealMat_augmentFloat`, `extended_f_eq_augment`) — handed to
`discretizeEnclosureFloat_mem_reach_horizon` for `N` steps. The control period is `N` times the
real time `toReal Δt` the float step denotes.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic
open Matrix ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is inside `reachFloat` at every
period boundary, the order admissible for the step at the augmented matrix. -/
theorem NeurNetContrSys.reachFloat_outer (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (o η N : ℕ) (ho : 0 < o) {Δt : 𝕋} (hΔt : 0 < toReal Δt)
    (hη : sys.augmentFloat.OrderAdmissibleFloat Δt Δt η) {H : ℕ} {R₀ : Zonotope (Vec 𝕋 n)}
    {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π) {W : Zonotope (Vec 𝕋 0)}
    {x : ℝ → Vec ℝ n} {w : ℝ → Vec ℝ 0}
    (traj : sys.Trajectory π ((N : ℝ) * toReal Δt) H R₀ W x w) :
    ∀ i ≤ H, x ((i : ℝ) * ((N : ℝ) * toReal Δt)) ∈
      construct (sys.reachFloat ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by -- --- PROOF ---
  have hNΔ : (0:ℝ) ≤ (N : ℝ) * toReal Δt := mul_nonneg (Nat.cast_nonneg N) hΔt.le
  obtain ⟨hA, hc⟩ := sys.toRealMat_augmentFloat
  refine sys.reachWith_timePoint_outer _ _ _
    (fun X Y x u hx hu => by
      show _ ∈ (X.cartProd Y).construct
      rw [Zonotope.cartProd_exact]
      exact ⟨(x, u), ⟨hx, hu⟩, rfl⟩)
    (fun Z z hz => Zonotope.project_outer Z (Fin.castAdd sys.plant.m) ⟨z, hz, rfl⟩) ?_ hπ traj
  -- a period of the extended system is a run of the augmented one, read in floats
  intro Z z w' hz
  have hcl : sys.augmentFloat.CanonicalClassicalTrajectory (S := 𝒵[𝕋])
      (Set.Icc 0 ((N : ℝ) * toReal Δt)) Z (Zonotope.point sys.augmentFloat.c) z
      (fun _ => Scalar.toRealVec sys.augmentFloat.c) :=
    ⟨hz.init, fun _ _ => by
      show _ ∈ (Zonotope.point sys.augmentFloat.c).construct
      rw [Zonotope.construct_point]
      rfl, fun t ht => by
      have h := hz.flow t ht
      rw [sys.extended_f_eq_augment, ← hA, ← hc] at h
      exact h⟩
  exact (hcl.trajectory (convex_Icc 0 _) ⟨le_rfl, hNΔ⟩
    (CompactSet.isBounded_construct _)).discretizeEnclosureFloat_mem_reach_horizon
    (K := N) hΔt subset_rfl hη ho N le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
