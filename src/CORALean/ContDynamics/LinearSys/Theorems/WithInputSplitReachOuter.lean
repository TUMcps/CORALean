module

public import CORALean.ContDynamics.LinearSys.Definitions.WithInputSplitReachExact
public import CORALean.ContDynamics.LinearSys.Operations.WithInputSplitReach
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindowExact
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMemConstInputSolution
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetParticularSolution
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reach` with the input set split encloses every run, one window at a time

[1, Alg. 3]'s soundness. A run is at `t ∈ τ_k` at
`e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds`; with `u = ũ + (u - ũ)` the integral is
`∫₀ᵗ e^{Aσ}dσ ũ` plus one admissible `Ũ`-input's contribution, and with
`t = t_k + τ` both the free motion and the constant's part are `e^{A t_k}` of
their values at `τ`, the constant's plus `P̃(t_k)` (`expIntegral_add_mulVec`).
At `τ ∈ [0, Δt]` those are in `H^R(τ_0)` and `P̃^R(τ_0)`, and the `Ũ` part is
in `P^R_Ũ(t_{k+1})`, `0 ∈ Ũ` being `Recenter`'s.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a run on `[0, tFinal - tStart]` from `X₀ = params.X₀`, under inputs in
`sys.U` wherever it sits, reaches is in one of `reach`'s windows. -/
theorem LinearSys.WithInputSplit.reach_outer (sys : LinearSys.WithInputSplit 𝕋 S n)
    (params : Reach.Params (S n) ℝ) {options : LinearSys.ReachStepOptions ℝ}
    (hΔt : 0 < options.Δt) : -- --- STMT ---
    sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
      ⊆ construct (sys.reach params options) := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tF⟩ := params
  obtain ⟨Δt, η⟩ := options
  unfold LinearSys.WithInputSplit.reach
  dsimp only at *
  generalize tF - tStart = tFinal at *
  rintro _ ⟨x, u, traj, t, ht, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * Δt := by push_cast; linarith
  have hτ0 : 0 ≤ t - k * Δt := sub_nonneg.mpr hkt
  have htk0 : 0 ≤ (k : ℝ) * Δt := by positivity
  -- the order `reach` runs at, `m + 2` in `timeIntervalStep_outer_at`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max η (sys.sys.reachOrder Δt + 2) = m + 2 :=
    ⟨max η (sys.sys.reachOrder Δt + 2) - 2, by omega⟩
  have hε : ‖Δt • toRealMat sys.sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    sys.sys.reachOrder_admissible Δt (hm ▸ le_max_right _ _)
  set A := toRealMat sys.sys.A with hA
  set uc := Recenter.center sys.U with huc
  -- the run on `[0, t]`, split into its free motion and its input's integral
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 tFinal := Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct (construct sys.U)) :=
    CompactSet.isBounded_construct sys.U
  have hvoc := traj.variation_of_constants hTt le_rfl ht.1 hU
  rw [sub_zero] at hvoc
  -- the input, split along `U ⊆ {ũ} ⊕ Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uc ∈ construct (Recenter.recenter sys.U) :=
    fun s hs => Recenter.sub_center_mem_recenter (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - uc) (volume.restrict (Set.Icc 0 t)) :=
    (traj.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (OfPoint.ofPoint uc : S n))
    (fun _ _ => OfPoint.mem_ofPoint uc) aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (Recenter.recenter sys.U)) hmem₀ hmeas₀
  have hsum : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      = (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ uc)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - uc) := by
    rw [← intervalIntegral.integral_add hint₁ hint₀]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  -- `t = t_k + τ`: the free motion and the constant's part, carried across `t_k`
  have hconst : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ uc)
      = exp (((k : ℝ) * Δt) • A) *ᵥ (MatExp.expIntegral A (t - k * Δt) *ᵥ uc)
        + MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ uc := by
    rw [MatExp.expIntegral_constInput A uc ht.1]
    have h := MatExp.expIntegral_add_mulVec A uc hτ0 htk0
    rwa [sub_add_cancel] at h
  -- `e^{At} = e^{A t_k} e^{Aτ}`, both powers of the same matrix
  have hexp : exp (t • A) *ᵥ x 0
      = exp (((k : ℝ) * Δt) • A) *ᵥ (exp ((t - k * Δt) • A) *ᵥ x 0) := by
    have hc : Commute (((k : ℝ) * Δt) • A) ((t - k * Δt) • A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x 0) h
  -- regrouped as the window's summands
  have hx : exp (t • A) *ᵥ x 0 + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s
      = (exp (((k : ℝ) * Δt) • A) *ᵥ (exp ((t - k * Δt) • A) *ᵥ x 0
            + MatExp.expIntegral A (t - k * Δt) *ᵥ uc)
          + MatExp.expIntegral A ((k : ℝ) * Δt) *ᵥ uc)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - uc) := by
    rw [hsum, hconst, hexp, Matrix.mulVec_add]
    abel
  -- window `k`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hvoc, hx]
    refine Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _
      (Set.add_mem_add ?_ (OfPoint.mem_ofPoint _))) ?_)
    · -- `e^{A t_k}` of a point of `H^R(τ_0) ⊕ P̃^R(τ_0)`
      refine Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _
        (Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_))))
      · exact sys.sys.timeIntervalStep_outer_at hΔt hε X₀ hτ0 htk
          (Set.mem_image_of_mem _ traj.init)
      · exact sys.sys.expIntegral_mem_constInputSolution hΔt (m + 2) hε uc hτ0 htk
    · -- one admissible `Ũ`-input's contribution by `t`, in `P^R_Ũ(t_{k+1})`
      exact sys.sys.inputReach_subset_particularSolution hΔt hε
        (Recenter.zero_mem_recenter sys.U) k ht.1 htk1 ⟨fun s => u s - uc, hmem₀, hmeas₀, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
