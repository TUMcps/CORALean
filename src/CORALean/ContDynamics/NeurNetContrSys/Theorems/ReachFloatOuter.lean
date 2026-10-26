module

public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachOuterOn
public import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
public import CORALean.ContDynamics.LinearSys.Theorems.DiscretizeHorizon
public import CORALean.ContDynamics.LinearSys.Theorems.ExpMemExpIntervalFloat
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputReach
public import CORALean.ContDynamics.LinearSys.Operations.StepInput
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.StepInputEqShifted
public import CORALean.ContDynamics.LinearSys.Theorems.StepSubsetHorizon
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
`aux_discretizeEnclosureFloat_mem_reach_horizon` for `N` steps. The control period is `N` times the
real time `toReal Δt` the float step denotes.

## Inputs
* `sys` – closed-loop system
* `U_ext` – external input zonotope
* `o` – maximum zonotope order
* `η` – Taylor order
* `N` – steps per period
* `Δt` – step size
* `H` – number of periods
* `R₀` – initial zonotope
* `π` – controller function
* `W` – disturbance set
* `x` – plant states
* `v` – external input signal
* `w` – disturbance signal

## Hypotheses
* `ho` – order positive
* `hΔt` – step positive
* `hdt` – the period is `N` steps
* `hη` – order admissible
* `hπ` – the network encloses `π`
* `hW` – disturbances sent to zero by the disturbance matrix
* `traj` – closed-loop trajectory

## Conclusion
* the state at every period boundary lies in the float reachable set
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open NormedSpace
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
open Scalar MeasureTheory
variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

/-- Translating by `c` carries `Icc (a-c) (b-c)` onto `Icc a b` and preserves
Lebesgue measure. -/
private theorem aux_aestronglyMeasurable_shift {f : ℝ → Vec ℝ n} {a b c : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b))) : -- --- CONCL ---
    AEStronglyMeasurable (fun σ => f (c + σ))
      (volume.restrict (Set.Icc (a - c) (b - c))) := by -- --- PROOF ---
  have hpre : (fun σ : ℝ => c + σ) ⁻¹' Set.Icc a b = Set.Icc (a - c) (b - c) := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have hmp : MeasurePreserving (fun σ : ℝ => c + σ)
      (volume.restrict (Set.Icc (a - c) (b - c))) (volume.restrict (Set.Icc a b)) := by
    rw [← hpre]
    exact (measurePreserving_add_left volume c).restrict_preimage measurableSet_Icc
  exact hf.comp_measurePreserving hmp


/-- Step `k`'s input contribution lies in `inputReach U Δt`, the domain covering
that step alone. -/
private theorem LinearSys.IsCanonicalTrajectory.aux_stepInput_mem_inputReach {sys : LinearSys 𝕋 n}
    {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {Δt : ℝ} (traj : sys.IsCanonicalTrajectory T R₀ U x u) (k : ℕ)
    (hT : Set.Icc ((k : ℝ) * Δt) (((k : ℝ) + 1) * Δt) ⊆ T) : -- --- CONCL ---
    sys.stepInput u Δt k ∈ sys.inputReach U Δt := by -- --- PROOF ---
  rw [show ((k : ℝ) + 1) * Δt = (k : ℝ) * Δt + Δt from by ring] at hT
  refine ⟨fun σ => u ((k : ℝ) * Δt + σ), fun σ hσ => traj.input _ (hT ⟨?_, ?_⟩), ?_,
    sys.stepInput_eq_shifted u Δt k⟩
  · linarith [hσ.1]
  · linarith [hσ.2]
  -- measurable on the step, then translated back to `[0, Δt]`
  have h := aux_aestronglyMeasurable_shift (c := (k : ℝ) * Δt)
    (traj.aestronglyMeasurable_input hT)
  simpa using h

end


section
open NormedSpace
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {n : ℕ} {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- Every sample `x (k Δt)`, `k ≤ K`, of a run on `[0, K Δt]` lies in the float-sampled
system's `reach` under the float input solution of `U`. -/
private theorem LinearSys.IsCanonicalTrajectory.aux_discretizeEnclosureFloat_mem_reach_horizon
    {sys : LinearSys 𝕋 n}
    {T : Set ℝ} {R₀ U : Zonotope (Vec 𝕋 n)} {x u : ℝ → Vec ℝ n} {Δt : 𝕋} {η K : ℕ}
    (traj : sys.IsCanonicalTrajectory (S := 𝒵[𝕋]) T R₀ U x u) (hΔt : 0 < toReal Δt)
    (hT : Set.Icc 0 ((K : ℝ) * toReal Δt) ⊆ T) (hη : sys.IsOrderAdmissibleFloat Δt Δt η)
    {o : ℕ} (ho : 0 < o) : -- --- CONCL ---
    ∀ k ≤ K, x ((k : ℝ) * toReal Δt) ∈ construct
    ((sys.discretizeEnclosureFloat Δt η).reach (S := 𝒵[𝕋])
      ⟨R₀, sys.inputSolutionFloat Δt η U, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  -- the exact sampling, every step's input inside the float input solution
  have hdt := traj.discretize_horizon (Ud := sys.inputSolutionFloat Δt η U) hΔt.le hT
    (CompactSet.isBounded_construct U) fun j hj =>
      sys.inputReach_subset_inputSolutionFloat hΔt hη U
        (traj.aux_stepInput_mem_inputReach j (step_subset_horizon hΔt.le hT hj))
  -- the same run, its matrix only enclosed
  have hon : (sys.discretizeEnclosureFloat Δt η).IsCanonicalTrajectoryOn (S := 𝒵[𝕋]) R₀
    (sys.inputSolutionFloat Δt η U) K
      (fun k : ℕ => x (k * toReal Δt)) (sys.stepInput u (toReal Δt)) :=
    { init := hdt.init
      input := hdt.input
      step := fun j hj => ⟨exp (toReal Δt • Scalar.toRealMat sys.A),
        sys.exp_mem_expIntervalFloat hη le_rfl le_rfl, by
          simpa [LinearSys.discretize] using hdt.step j hj⟩ }
  exact fun k hk => (sys.discretizeEnclosureFloat Δt η).reach_outer_on
    (S := 𝒵[𝕋]) ho R₀ _ hon k hk

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every zero-order-hold run of `H` control periods is inside `reachFloat` at every
period boundary, the order admissible for the step at the augmented matrix. -/
theorem NeurNetContrSys.reachFloat_outer (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (U_ext : Zonotope (Vec 𝕋 sys.nExt)) (o η N : ℕ) (ho : 0 < o) {Δt : 𝕋}
    (hΔt : 0 < toReal Δt) (hdt : sys.dt = (N : ℝ) * toReal Δt)
    (hη : sys.augmentFloat.IsOrderAdmissibleFloat Δt Δt η) {H : ℕ} {R₀ : Zonotope (Vec 𝕋 n)}
    {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Encloses π)
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, Scalar.toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : sys.IsTrajectory π H R₀ (construct U_ext) W x v w) : -- --- CONCL ---
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
  have hcl : sys.augmentFloat.IsCanonicalTrajectory (S := 𝒵[𝕋])
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
  exact hcl.aux_discretizeEnclosureFloat_mem_reach_horizon
    (K := N) hΔt (Set.Icc_subset_Icc_right hdt.ge) hη ho N le_rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
