import CORALean.ContDynamics.LinParamSys.Operations.ReachFloatInput
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolutionFloat
import CORALean.ContDynamics.LinParamSys.Theorems.MapMEqSome
import CORALean.ContDynamics.LinParamSys.Theorems.ReachFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# `LinParamSys.reachFloatInput` holds every member's run at every time of every window

`reachFloat_outer` with an input: a constant-parameter run fixes one member `A`, and is
the point system `⟨A⟩`'s run (`toLinearSys`), so at `t = t_k + s` it is at
`e^{At} x(0) + ∫₀ᵗ e^{A(t-σ)} u(σ) dσ`. The first term is `e^{A t_k}` of `e^{As} x(0)`,
in the first window by `timeIntervalStepFloat_outer` and carried by `reachStepkFloat_outer`;
the second is in `P^R(t_{k+1})` (`inputReach_subset_particularSolutionFloat`, where `0 ∈ U`
is spent), both at `A`.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinParamSys.reachFloatInput_outer (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    {U : Zonotope (Vec 𝕋 n)} (h0 : (0 : Vec ℝ n) ∈ U.construct)
    {params : Reach.Params (Zonotope (Vec 𝕋 n)) ℚ} {options : LinearSys.ReachOptions 𝕋}
    {Rs : List (Zonotope (Vec 𝕋 n))} (h : sys.reachFloatInput U params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ {A : Mat ℝ n n} {x u : ℝ → Vec ℝ n},
        sys.ConstTrajectory (S := fun k => Zonotope (Vec 𝕋 k))
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart))
          params.X₀ U x u A →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
          (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinParamSys.reachFloatInput, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨N, hN, η', hη', hRs⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinParamSys.reachOrderFloat_spec hη').1
  obtain ⟨hlen, hget⟩ := LinParamSys.mapM_eq_some hRs
  rw [List.length_range] at hlen
  refine ⟨N, hNΔt, hlen, fun {A x u} traj k hk t ht => ?_⟩
  have hwin := hget k hk
  simp only [List.getElem_range, LinParamSys.reachStepkFloatInput, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hwin
  obtain ⟨H, hH, P, hP, hRk⟩ := hwin
  -- window `k` lies inside the horizon
  have hkN : ((k : ℝ) + 1) * toReal Δt ≤ (tFinal : ℝ) - tStart := by
    rw [← hNΔt]
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hlen ▸ hk
    exact mul_le_mul_of_nonneg_right this hΔt.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * toReal Δt := by positivity
  have ht0 : 0 ≤ t := le_trans hk0 ht.1
  have hτ : t - k * toReal Δt ∈ Set.Icc 0 (toReal Δt) := ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 ((tFinal : ℝ) - tStart) :=
    Set.Icc_subset_Icc_right (ht.2.trans hkN)
  -- the run is the point system `⟨A⟩`'s, split into its free motion and its input's integral
  have lin := traj.toLinearSys
  have hvoc := lin.variation_of_constants hTt le_rfl ht0
    (CompactSet.isBounded_construct U)
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  -- that integral is one admissible input's contribution by `t`, under `A`
  have hin : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ (LinearSys.mk A : LinearSys ℝ n).inputReach (S := fun k => Zonotope (Vec 𝕋 k)) U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), lin.aestronglyMeasurable_input hTt, by
      simp only [Scalar.toRealMat_real]⟩
  -- `e^{At} = e^{A t_k} e^{Aτ}`, both powers of the same member
  have hexp : exp (t • A) *ᵥ x 0
      = exp (((k : ℝ) * toReal Δt) • A) *ᵥ (exp ((t - k * toReal Δt) • A) *ᵥ x 0) := by
    have hc : Commute (((k : ℝ) * toReal Δt) • A) ((t - k * toReal Δt) • A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x 0) h
  have hτ₀ := Reduce.reduce_outer (sys.timeIntervalStepFloat Δt η' X₀) ρ
    (sys.timeIntervalStepFloat_outer hΔt hadm X₀ traj.param traj.init hτ.1 hτ.2)
  have hfree := sys.reachStepkFloat_outer hadm.1 hH traj.param hτ₀
  have hinput := sys.inputReach_subset_particularSolutionFloat hΔt hadm traj.param h0 hP ht0
    (by push_cast; linarith [ht.2]) hin
  rw [← hRk, hvoc, hexp]
  exact Plus.plus_outer H P (Set.add_mem_add hfree hinput)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
