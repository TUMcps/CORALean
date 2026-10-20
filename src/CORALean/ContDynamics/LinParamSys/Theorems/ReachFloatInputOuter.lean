module

public import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatInput
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryCanonical
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstPropagateFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolutionFloat
public import CORALean.ContDynamics.LinParamSys.Theorems.MapMEqSome
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.Zonotope.Float.Theorems.ConstructPoint

@[expose] public section

/-!
# `LinParamSys.reachFloatInput` holds every member's run at every time of every window

A run fixes `A` and `B`, and its combined input `B u + sys.c` lies in `V = B U ⊕ c` (`c` the float
vector that is `sys.c` through `toRealVec`), so it is a run of the canonical form under `V`, the
point system `⟨A⟩`'s run (`toLinearSys`): at `t` it is at `e^{At} x(0) + ∫₀ᵗ e^{A(t-σ)} u'(σ) dσ`.
With `u' = ũ + (u' - ũ)` the integral is `∫₀ᵗ e^{Aσ}dσ ũ` plus one admissible `Ũ`-input's
contribution, and with `t = t_k + s` both the free motion and the constant's part are `e^{A t_k}`
of their values at `s` (`expIntegral_add_mulVec`). At `s ∈ [0, Δt]` those are in `H^R(τ_0)` and
`P̃^R(τ_0)`, `P̃(t_k)` is `expIntegral_mem_constPropagateFloat`, and `0 ∈ Ũ` is `Recenter`'s.

## Inputs
* `sys` – system
* `c` – offset as a float vector
* `params` – reachability parameters with inputs
* `options` – reachability options

## Hypotheses
* `hc` – `c` is the system offset

## Conclusion
* the returned windows hold every constant-parameter run at every time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The windows `reachFloatInput` returns hold every constant-parameter run of the system, at
every time of the window, under inputs in `params.U` (input coordinates) anywhere. -/
theorem LinParamSys.reachFloatInput_outer (sys : LinParamSys ℐ[𝕋] n) {c : Vec 𝕋 n}
    (hc : Scalar.toRealVec c = sys.c)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} : -- --- CONCL ---
    ∀ Rs ∈ sys.reachFloatInput c params options,
      ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
        Rs.length = N ∧ ∀ {A : Mat ℝ n n} {B : Mat ℝ n sys.m} {x : ℝ → Vec ℝ n}
          {u : ℝ → Vec ℝ sys.m},
          sys.IsConstTrajectory (S := 𝒵[𝕋])
            (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart))
            params.X₀ params.U x u A B →
          ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
            (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  intro Rs (h : sys.reachFloatInput c params options = some Rs)
  obtain ⟨X₀, U, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinParamSys.reachFloatInput, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', hRs⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal _ hN
  have hadm := (LinParamSys.reachOrderFloat_spec _ hη').1
  obtain ⟨hlen, hget⟩ := LinParamSys.mapM_eq_some hRs
  rw [List.length_range] at hlen
  refine ⟨N, hNΔt, hlen, fun {A B x uIn} trajB k hk t ht => ?_⟩
  have hwin := hget k hk
  simp only [List.getElem_range, LinParamSys.aux_reachStepkFloatInput, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hwin
  obtain ⟨Hτk, hH, PRtk, hP, hRk⟩ := hwin
  -- the input set of the state space, `B U`
  set V : Zonotope (Vec 𝕋 n) := Mtimes.mtimes (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) sys.B U
    ⊞ Zonotope.point c with hV
  set Δ := toReal Δt with hΔ
  -- the split's center `ũ`, the stored one
  set uc : Vec 𝕋 n := ScalarCenter.centerVec (S := 𝒵[𝕋]) V with huc
  set ũ : Vec ℝ n := Scalar.toRealVec uc with hũ
  have hũc : ũ = Recenter.center V := rfl
  -- the run's combined input `B u` lies in `V = B U`: a run of the canonical form under `V`
  obtain ⟨u, traj⟩ : ∃ u : ℝ → Vec ℝ n, sys.IsCanonicalConstTrajectory (S := 𝒵[𝕋])
      (Set.Icc 0 ((tFinal : ℝ) - tStart)) X₀ V x u A := by
    refine ⟨_, trajB.canonical fun s hs => ?_⟩
    have hBu : B *ᵥ uIn s ∈ (B *ᵥ ·) '' construct U := ⟨uIn s, trajB.input s hs, rfl⟩
    exact Plus.plus_outer _ _ (Set.add_mem_add
      (Mtimes.mtimes_outer (𝕄 := ℐ[𝕋]) (S := 𝒵[𝕋]) sys.B U
        (Set.mem_iUnion₂.mpr ⟨B, trajB.paramB, hBu⟩))
      (show sys.c ∈ (Zonotope.point c).construct by
        rw [Zonotope.construct_point, Set.mem_singleton_iff]; exact hc.symm))
  -- window `k` lies inside the horizon
  have hkN : ((k : ℝ) + 1) * Δ ≤ (tFinal : ℝ) - tStart := by
    rw [← hNΔt]
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hlen ▸ hk
    exact mul_le_mul_of_nonneg_right this hΔt.le
  have htk0 : (0 : ℝ) ≤ (k : ℝ) * Δ := by positivity
  have ht0 : 0 ≤ t := le_trans htk0 ht.1
  have hτ0 : 0 ≤ t - k * Δ := sub_nonneg.mpr ht.1
  have htk : t - k * Δ ≤ Δ := by linarith [ht.2]
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * Δ := by push_cast; linarith [ht.2]
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 ((tFinal : ℝ) - tStart) :=
    Set.Icc_subset_Icc_right (ht.2.trans hkN)
  -- the run is the point system `⟨A⟩`'s, split into its free motion and its input's integral
  have lin := traj.toLinearSys
  have hU : Bornology.IsBounded (construct (construct V)) := CompactSet.isBounded_construct V
  have hvoc := lin.variation_of_constants hTt le_rfl ht0 hU
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  -- the input, split along `V ⊆ {ũ} ⊞ Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - ũ ∈ construct (Recenter.recenter V) :=
    fun s hs => Recenter.sub_center_mem_recenter (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - ũ) (volume.restrict (Set.Icc 0 t)) :=
    (lin.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (S := 𝒵[𝕋])
    (A := A) (c := t) ht0
    (CompactSet.isBounded_construct
      (OfScalarPoint.ofVec (S := 𝒵[𝕋]) uc : Zonotope (Vec 𝕋 n)))
    (fun _ _ => OfScalarPoint.mem_ofVec (S := 𝒵[𝕋]) uc)
      aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (S := 𝒵[𝕋])
    (A := A) (c := t) ht0
    (CompactSet.isBounded_construct (Recenter.recenter V)) hmem₀ hmeas₀
  have hsum : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      = (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ ũ)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - ũ) := by
    rw [← intervalIntegral.integral_add hint₁ hint₀]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Matrix.mulVec_add, add_sub_cancel]
  -- `t = t_k + s`: the constant's part, carried across `t_k`
  have hconst : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ ũ)
      = exp (((k : ℝ) * Δ) • A) *ᵥ (Real.MatExp.expIntegral A (t - k * Δ) *ᵥ ũ)
        + Real.MatExp.expIntegral A ((k : ℝ) * Δ) *ᵥ ũ := by
    rw [Real.MatExp.expIntegral_constInput A ũ ht0]
    have h := Real.MatExp.expIntegral_add_mulVec A ũ hτ0 htk0
    rwa [sub_add_cancel] at h
  -- `e^{At} = e^{A t_k} e^{As}`, both powers of the same member
  have hexp : exp (t • A) *ᵥ x 0
      = exp (((k : ℝ) * Δ) • A) *ᵥ (exp ((t - k * Δ) • A) *ᵥ x 0) := by
    have hc : Commute (((k : ℝ) * Δ) • A) ((t - k * Δ) • A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x 0) h
  -- regrouped as the window's summands
  have hx : x t = (exp (((k : ℝ) * Δ) • A) *ᵥ (exp ((t - k * Δ) • A) *ᵥ x 0
            + Real.MatExp.expIntegral A (t - k * Δ) *ᵥ ũ)
          + Real.MatExp.expIntegral A ((k : ℝ) * Δ) *ᵥ ũ)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - ũ) := by
    rw [hvoc, hsum, hconst, hexp, Matrix.mulVec_add]
    abel
  -- the first window holds the free motion and the constant's share at `s`
  have hfirst : exp ((t - k * Δ) • A) *ᵥ x 0 + Real.MatExp.expIntegral A (t - k * Δ) *ᵥ ũ
      ∈ construct (Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀
        ⊞ sys.constInputSolutionFloat Δt η' uc) ρ) :=
    Reduce.reduce_outer _ ρ (Plus.plus_outer (sys.timeIntervalStepFloat Δt η' X₀)
      (sys.constInputSolutionFloat Δt η' uc) (Set.add_mem_add
        (sys.timeIntervalStepFloat_outer hΔt hadm X₀ traj.param traj.init hτ0 htk)
        (sys.expIntegral_mem_constInputSolutionFloat hΔt hadm traj.param uc hτ0 htk)))
  have hHτ := sys.reachStepkFloat_outer hadm.1 traj.param hfirst _ hH
  have hPc := sys.expIntegral_mem_constPropagateFloat ρ hΔt hadm traj.param uc k
  have hPR : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - ũ)) ∈ PRtk.construct :=
    sys.inputReach_subset_particularSolutionFloat hΔt hadm traj.param
    (Recenter.zero_mem_recenter V) ht0 htk1 _ hP
    ⟨fun s => u s - ũ, hmem₀, hmeas₀, by simp only [Scalar.toRealMat_real]⟩
  rw [← hRk, hx]
  exact Plus.plus_outer _ PRtk (Set.add_mem_add
    (Plus.plus_outer Hτk _ (Set.add_mem_add hHτ hPc)) hPR)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
