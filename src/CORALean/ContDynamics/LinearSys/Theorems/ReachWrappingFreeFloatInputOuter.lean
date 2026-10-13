import CORALean.ContDynamics.Reach.Theorems.StepsSpecToReal
import CORALean.ContDynamics.LinParamSys.Theorems.MapMEqSome
import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFreeFloatInput
import CORALean.ContDynamics.LinearSys.Theorems.ExpAddSmul
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSeparationSubset
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolutionFloat
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderFloatSpec
import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkWrappingFreeFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepFloatOuter
import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre

/-!
# `reachWrappingFreeFloatInput` holds every run over every window

At `t = τ + t_k`: the run less its free motion and the constant's share is one
`Ũ`-input's contribution by `t` (`Trajectory.sub_mem_inputReach_recentre`),
inside `e^{A t_k} P^R(Δt) ⊕ P^R(t_k)` (`inputReach_mono`, then
`inputReach_separation_subset` at `Δt + t_k`); the free motion and the constant
come apart the same way (`expIntegral_add_mulVec`). So the run is
`e^{A t_k}` of a point of `Rτ₀ ⊕ P^R(Δt)`, which `reachStepkWrappingFreeFloat_outer`
carries, plus a point of `P̃(t_k) ⊕ P^R(t_k)`, which the accumulation holds by
induction on `k`, from `{0}` at `t_0 = 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic NormedSpace Matrix MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U` is,
at every time of window `k`, in the `k`-th set. -/
theorem LinearSys.reachWrappingFreeFloatInput_outer (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rs : List (Zonotope (Vec 𝕋 n))}
    (h : sys.reachWrappingFreeFloatInput B params options = some Rs) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rs.length = N ∧ ∀ {x u : ℝ → Vec ℝ n},
        sys.Trajectory (S := fun k => Set (Vec ℝ k))
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          ((Scalar.toRealMat B *ᵥ ·) '' params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < Rs.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
          (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rs[k].construct := by -- --- PROOF ---
  obtain ⟨X₀, U, tStart, tFinal⟩ := params
  obtain ⟨Δt, η, ρ⟩ := options
  dsimp only at h ⊢
  simp only [LinearSys.reachWrappingFreeFloatInput, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨N, hN, η', hη', Hτ, hHτ, Pτ, hPτ, rfl⟩ := h
  obtain ⟨hΔt, hNΔt⟩ := Reach.steps_spec_toReal hN
  have hadm := (LinearSys.reachOrderFloat_spec hη').1
  obtain ⟨hHlen, hHget⟩ := LinParamSys.mapM_eq_some hHτ
  obtain ⟨hPlen, hPget⟩ := LinParamSys.mapM_eq_some hPτ
  rw [List.length_range] at hHlen hPlen
  refine ⟨N, hNΔt, by simp [hHlen, hPlen], fun {x u} traj k hk t ht => ?_⟩
  set Δ := toReal Δt with hΔ
  set V := Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B U with hV
  set A := Scalar.toRealMat sys.A with hA
  set ũ := Recentre.centre V with hũ
  set Ũ := Recentre.recentre V with hŨ
  have hbdd := CompactSet.isBounded_construct Ũ
  -- `{0}`, `{ũ}` and `[0, ũ]` hold what they are built from
  have hpt : ũ ∈ (Interval.point V.c).zonotope.construct :=
    Interval.zonotope_contains _ (Interval.mem_point V.c)
  have hzero : (0 : Vec ℝ n) ∈ (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope.construct := by
    have h0 := Interval.zonotope_contains _ (Interval.mem_point fun _ : Fin n => (zero : 𝕋))
    rwa [show RealImage.realImage (fun _ : Fin n => (zero : 𝕋)) = (0 : Vec ℝ n) from
      funext fun _ => toReal_zero] at h0
  -- the segment `[0, ũ]` holds both its ends
  set seg := LinComb.linComb (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
    (Interval.point V.c).zonotope with hseg
  have h0seg : (0 : Vec ℝ n) ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, hzero, ũ, hpt, 1, ⟨zero_le_one, le_rfl⟩, by simp⟩
  have hũseg : ũ ∈ seg.construct := by
    refine LinComb.linComb_outer (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope
      (Interval.point V.c).zonotope ?_
    exact ⟨0, hzero, ũ, hpt, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  -- the constant `ũ` held over `[0, τ]` is an admissible input of any set holding `ũ`
  have hconst : ∀ {W : Zonotope (Vec 𝕋 n)}, ũ ∈ W.construct → ∀ {τ : ℝ}, 0 ≤ τ →
      Real.MatExp.expIntegral A τ *ᵥ ũ ∈ sys.inputReach (S := fun k => Zonotope (Vec 𝕋 k)) W τ :=
    fun hW _ hτ => ⟨fun _ => ũ, fun _ _ => hW, aestronglyMeasurable_const,
      (Real.MatExp.expIntegral_constInput A ũ hτ).symm⟩
  have hPu := sys.inputReach_subset_inputSolutionFloat hΔt hadm _ (hconst hpt hΔt.le)
  have hPU := sys.inputReach_subset_inputSolutionFloat hΔt hadm Ũ
  -- the accumulation holds the constant's share by `t_j` plus any `Ũ`-input's
  set P := Pτ.scanl (fun P Q => Reduce.reduce (P ⊞ Q) ρ)
    (Interval.point fun _ : Fin n => (zero : 𝕋)).zonotope with hPdef
  have hP : ∀ (j : ℕ) (hj : j < P.length), ∀ q ∈ sys.inputReach (S := fun k => Zonotope (Vec 𝕋 k)) Ũ
    ((j : ℝ) * Δ),
      Real.MatExp.expIntegral A ((j : ℝ) * Δ) *ᵥ ũ + q ∈ ContSet.construct P[j] := by
    intro j
    induction j with
    | zero =>
      -- at `t_0 = 0` nothing has been contributed, and `{0}` holds that
      intro _ q hq
      obtain ⟨_, -, -, rfl⟩ := hq
      simp only [hPdef, List.getElem_scanl_zero, Nat.cast_zero, zero_mul,
        intervalIntegral.integral_same, add_zero]
      have hz : Real.MatExp.expIntegral A 0 = 0 := by simp [Real.MatExp.expIntegral]
      rw [hz, Matrix.zero_mulVec]
      exact hzero
    | succ j ih =>
      -- the share by `t_{j+1}` comes apart at `Δt`
      intro hj q hq
      have hjN : j < Pτ.length := by simp [hPdef] at hj; omega
      simp only [hPdef, List.getElem_succ_scanl]
      have ht' : ((j + 1 : ℕ) : ℝ) * Δ = Δ + (j : ℝ) * Δ := by push_cast; ring
      rw [ht'] at hq ⊢
      obtain ⟨_, ⟨p, hp, rfl⟩, q', hq', rfl⟩ := sys.inputReach_separation_subset
        (S := fun k => Zonotope (Vec 𝕋 k)) hΔt.le
        (by positivity) hbdd hq
      -- the step's share, carried across `t_j` by `[e^{A t_j}]`
      have hstep := sys.reachStepkWrappingFreeFloat_outer hadm.1 (hPget j hjN)
        (Plus.plus_outer (sys.inputSolutionFloat Δt η' (Interval.point V.c).zonotope)
          (sys.inputSolutionFloat Δt η' Ũ) (Set.add_mem_add hPu (hPU hp)))
      simp only [List.getElem_range] at hstep
      rw [Matrix.mulVec_add] at hstep
      have hsum := Reduce.reduce_outer _ ρ (Plus.plus_outer P[j] Pτ[j] (Set.add_mem_add
        (ih (by simp [hPdef] at hj ⊢; omega) q' hq') hstep))
      rw [Real.MatExp.expIntegral_add_mulVec A ũ hΔt.le (by positivity)]
      convert hsum using 1
      simp only [← hA, ← hΔ]
      abel
  -- window `k` lies inside the horizon
  have hkN : ((k : ℝ) + 1) * Δ ≤ (tFinal : ℝ) - tStart := by
    rw [← hNΔt]
    have : (k : ℝ) + 1 ≤ N := by
      have : k < N := by simp [hHlen] at hk; omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this hΔt.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * Δ := by positivity
  have ht0 : 0 ≤ t := le_trans hk0 ht.1
  have hτ : t - k * Δ ∈ Set.Icc 0 Δ := ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩
  -- the run's inputs are in `B U`'s float enclosure
  have hUV : ContSet.construct ((Scalar.toRealMat B *ᵥ ·) '' U.construct)
      ⊆ ContSet.construct V := by
    rintro _ ⟨w, hw, rfl⟩
    exact Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) B U
      (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hw))
  have hd := traj.sub_mem_inputReach_recentre (S' := fun k => Zonotope (Vec 𝕋 k)) hUV
    ⟨ht0, ht.2.trans hkN⟩
  -- the `Ũ`-input's share by `t`: its first step carried across `t_k`, and the rest
  have hd' := sys.inputReach_mono (S := fun k => Zonotope (Vec 𝕋 k)) hbdd
    (Recentre.zero_mem_recentre V) ht0
    (show t ≤ Δ + (k : ℝ) * Δ by linarith [ht.2]) hd
  obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, hpq⟩ := sys.inputReach_separation_subset
    (S := fun k => Zonotope (Vec 𝕋 k))
    hΔt.le hk0 hbdd hd'
  -- the free motion and the constant's share in the first window, carried to `t_k`
  have hfirst : exp ((t - k * Δ) • A) *ᵥ x 0 + Real.MatExp.expIntegral A (t - k * Δ) *ᵥ ũ
      ∈ ContSet.construct (Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀
        ⊞ sys.inputSolutionFloat Δt η' seg) ρ) :=
    Reduce.reduce_outer _ ρ (Plus.plus_outer _ _ (Set.add_mem_add
      (sys.timeIntervalStepFloat_outer hΔt hadm X₀ traj.init hτ.1 hτ.2)
      (sys.inputReach_subset_inputSolutionFloat hΔt hadm seg
        (sys.inputReach_mono (S := fun k => Zonotope (Vec 𝕋 k)) (CompactSet.isBounded_construct seg)
          h0seg hτ.1 hτ.2
          (hconst hũseg hτ.1)))))
  have hk' : k < N := by simp [hHlen] at hk; omega
  have hwin := sys.reachStepkWrappingFreeFloat_outer hadm.1 (hHget k (by rw [hHlen]; exact hk'))
    (Plus.plus_outer (Reduce.reduce (sys.timeIntervalStepFloat Δt η' X₀
      ⊞ sys.inputSolutionFloat Δt η' seg) ρ) (sys.inputSolutionFloat Δt η' Ũ)
      (Set.add_mem_add hfirst (hPU hp)))
  simp only [List.getElem_range] at hwin
  have hacc := hP k (by simp [hPdef, hPlen]; omega) q hq

  have hkH : k < Hτ.length := by rw [hHlen]; exact hk'
  have hkP : k < P.length := by simp [hPdef, hPlen]; omega
  have hx := Plus.plus_outer (Hτ[k]'hkH) (P[k]'hkP) (Set.add_mem_add hwin hacc)
  -- `x(t)` regrouped as the window's two summands
  have hsplit : t = (t - k * Δ) + (k : ℝ) * Δ := by ring
  have hfree : exp (t • A) *ᵥ x 0
      = exp (((k : ℝ) * Δ) • A) *ᵥ (exp ((t - k * Δ) • A) *ᵥ x 0) := by
    conv_lhs => rw [hsplit]
    rw [add_comm (t - k * Δ) ((k : ℝ) * Δ), exp_add_smul_eq_mul, Matrix.mulVec_mulVec]
  have hconstk := Real.MatExp.expIntegral_add_mulVec A ũ hτ.1 hk0
  rw [← hsplit] at hconstk
  rw [eq_sub_iff_add_eq, ← hA] at hpq
  beta_reduce at hpq
  have heq : x t = exp (((k : ℝ) * Δ) • A) *ᵥ ((exp ((t - k * Δ) • A) *ᵥ x 0
        + Real.MatExp.expIntegral A (t - k * Δ) *ᵥ ũ) + p)
      + (Real.MatExp.expIntegral A ((k : ℝ) * Δ) *ᵥ ũ + q) := by
    rw [← hpq, hfree, hconstk, Matrix.mulVec_add, Matrix.mulVec_add]
    abel
  rw [List.getElem_zipWith, heq]
  exact hx

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
