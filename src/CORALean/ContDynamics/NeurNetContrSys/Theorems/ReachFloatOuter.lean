module

public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeEnclosureFloatHorizon
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.AugmentFlow
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
matrices reading as the real ones (`toRealMat_augmentFloat`, `augment_flow`) — handed to
`discretizeEnclosureFloat_mem_reach_horizon` for `N` steps. The control period is `N` times the
real time `toReal Δt` the float step denotes.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
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
    (U_ext : Zonotope (Vec 𝕋 sys.nExt)) (o η N : ℕ) (ho : 0 < o) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) (hdt : sys.dt = (N : ℝ) * toReal Δt)
    (hη : sys.augmentFloat.OrderAdmissibleFloat Δt Δt η) {H : ℕ} {R₀ : Zonotope (Vec 𝕋 n)}
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, Scalar.toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.Trajectory π H R₀ (construct U_ext) W x v w) :
    ∀ i ≤ H, x ((i : ℝ) * sys.dt) ∈
      construct (sys.reachFloat U_ext ⟨R₀, 0, i⟩ ⟨Δt, N, η, o, ho⟩) := by -- --- PROOF ---
  obtain ⟨hA, hc, hB⟩ := sys.toRealMat_augmentFloat
  refine sys.reachWith_timePoint_outer _ _ _
    (fun X Y x u hx hu => by
      show _ ∈ (X.cartProd Y).construct
      rw [Zonotope.cartProd_exact]
      exact ⟨(x, u), ⟨hx, hu⟩, rfl⟩)
    (fun Z z hz => Zonotope.project_outer Z (Fin.castAdd sys.m) ⟨z, hz, rfl⟩) ?_ hπ traj
  -- a period of the plant is a run of the augmented system, read in floats
  intro Z z u v' w' hz hzt
  obtain ⟨hcont, hvU, hmeas, hflow⟩ :=
    sys.augment_flow (CompactSet.isBounded_construct U_ext) hW hzt
  -- the augmented input `B_aug v + c_aug` is in `B_aug U_ext ⊕ [c; 0]`
  have hin : ∀ t ∈ Set.Icc 0 sys.dt,
      Scalar.toRealMat sys.augmentFloat.B *ᵥ v' t + Scalar.toRealVec sys.augmentFloat.c ∈
        construct (Plus.plus (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) sys.augmentFloat.B U_ext)
          (Zonotope.point sys.augmentFloat.c) : Zonotope (Vec 𝕋 (n + sys.m))) := fun t ht => by
    refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · exact Mtimes.mtimes_outer _ _
        (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ (hvU t ht)))
    · show _ ∈ (Zonotope.point sys.augmentFloat.c).construct
      rw [Zonotope.construct_point]
      rfl
  -- the period as a canonical run of the float system, its input read back through `hB`, `hc`
  have hcl : sys.augmentFloat.CanonicalTrajectory (S := 𝒵[𝕋])
      (Set.Icc 0 sys.dt) Z
      (Plus.plus (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) sys.augmentFloat.B U_ext)
        (Zonotope.point sys.augmentFloat.c))
      (fun t => Fin.append (z t) u)
      (fun t => Scalar.toRealMat sys.augmentFloat.B *ᵥ v' t +
        Scalar.toRealVec sys.augmentFloat.c) :=
    ⟨hz, hin, by rw [hB, hc]; exact hmeas, hcont, fun t ht => by
      rw [hA, hB, hc]
      exact hflow t ht⟩
  rw [hdt]
  exact hcl.discretizeEnclosureFloat_mem_reach_horizon
    (K := N) hΔt (Set.Icc_subset_Icc_right hdt.ge) hη ho N le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
