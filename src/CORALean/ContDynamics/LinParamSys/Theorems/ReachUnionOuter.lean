module

public import CORALean.ContDynamics.LinParamSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.LinParamSys.Operations.ReachUnion
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryCanonical
public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstPropagate
public import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.IsTrajectoryMemInputSet
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindowExact
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
public import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reachUnion` encloses every constant-parameter run

[1, Alg. 1]'s soundness, the input set anywhere. A run fixes `A` and `B`, and its combined input
`B u + c` lies in `V = B U ⊕ c` (`mem_inputSet`), so it is a run of the canonical form under
`V`, the point system `⟨A⟩`'s (`toLinearSys`): at `t` it is at
`e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u'(s) ds`.
With `u' = ũ + (u' - ũ)` the integral is `∫₀ᵗ e^{Aσ}dσ ũ` plus one admissible `Ũ`-input's
contribution, and with `t = t_k + τ` both the free motion and the constant's part are
`e^{A t_k}` of their values at `τ`, the constant's plus `P̃(t_k)` (`expIntegral_add_mulVec`).
At `τ ∈ [0, Δt]` those are in `H^R(τ_0)` and `P̃^R(τ_0)`, `P̃(t_k)` is
`expIntegral_mem_constPropagate`, and the `Ũ` part is in `P^R_Ũ(t_{k+1})`, `0 ∈ Ũ` being
`Recenter`'s: no hypothesis on `U` holds the origin.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Sonnet 5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recenter (S n) (Vec ℝ n)] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a constant-parameter run on `[0, tFinal - tStart]` from `X₀`, under inputs in
`params.U` (input coordinates) wherever it sits, reaches is in one of `reachUnion`'s windows. -/
theorem LinParamSys.reachUnion_outer (sys : LinParamSys ℐ n)
    (params : Reach.InputParams (S n) (S sys.m) ℝ) {options : LinearSys.ReachStepOptions ℝ}
    (hΔt : 0 < options.Δt) : -- --- CONCL ---
    sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
      (construct params.U) ⊆ construct (sys.reachUnion params options) := by -- --- PROOF ---
  rintro _ ⟨A, B, x, uIn, trajB, t, ht, rfl⟩
  -- the combined input `B u + c` lies in `V = B U ⊕ c`, which makes the run canonical under `V`
  set V := sys.inputSet params.U with hV
  obtain ⟨u, traj⟩ : ∃ u : ℝ → Vec ℝ n, sys.IsCanonicalConstTrajectory (S := 𝒮)
      (Set.Icc 0 (params.tFinal - params.tStart)) (construct params.X₀) (construct V) x u A :=
    ⟨_, trajB.canonical fun s hs => sys.mem_inputSet trajB.paramB (trajB.input s hs)⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * options.Δt := by push_cast; linarith
  have hτ0 : 0 ≤ t - k * options.Δt := sub_nonneg.mpr hkt
  have htk0 : 0 ≤ (k : ℝ) * options.Δt := mul_nonneg (Nat.cast_nonneg k) hΔt.le
  -- the order `reachUnion` runs at, `m + 2` in `reachStepk_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max options.η (sys.reachOrder options.Δt + 2) = m + 2 :=
    ⟨max options.η (sys.reachOrder options.Δt + 2) - 2, by omega⟩
  have hε : ‖(Interval.smul options.Δt sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    have hadm := sys.reachOrder_admissible options.Δt
    have hle : ((sys.reachOrder options.Δt + 2 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast hm ▸ le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) hadm
  set uc := Recenter.center V with huc
  -- the run is the point system `⟨A⟩`'s, split into its free motion and its input's integral
  have trajL := traj.toLinearSys
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 (params.tFinal - params.tStart) :=
    Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct (construct V)) :=
    CompactSet.isBounded_construct V
  have hvoc := trajL.variation_of_constants hTt le_rfl ht.1 hU
  simp only [sub_zero, Scalar.toRealMat_real] at hvoc
  -- the input, split along `U ⊆ {ũ} ⊞ Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uc ∈ construct (Recenter.recenter V) :=
    fun s hs => Recenter.sub_center_mem_recenter (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - uc) (volume.restrict (Set.Icc 0 t)) :=
    (trajL.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (OfPoint.ofPoint uc : S n))
    (fun _ _ => OfPoint.mem_ofPoint uc) aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (Recenter.recenter V)) hmem₀ hmeas₀
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
      = exp (((k : ℝ) * options.Δt) • A)
          *ᵥ (MatExp.expIntegral A (t - k * options.Δt) *ᵥ uc)
        + MatExp.expIntegral A ((k : ℝ) * options.Δt) *ᵥ uc := by
    rw [MatExp.expIntegral_constInput A uc ht.1]
    have h := MatExp.expIntegral_add_mulVec A uc hτ0 htk0
    rwa [sub_add_cancel] at h
  -- `e^{At} = e^{A t_k} e^{Aτ}`, both powers of the same member
  have hexp : exp (t • A) *ᵥ x 0
      = exp (((k : ℝ) * options.Δt) • A)
          *ᵥ (exp ((t - k * options.Δt) • A) *ᵥ x 0) := by
    have hc : Commute (((k : ℝ) * options.Δt) • A) ((t - k * options.Δt) • A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x 0) h
  -- regrouped as the window's summands
  have hx : exp (t • A) *ᵥ x 0 + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s
      = (exp (((k : ℝ) * options.Δt) • A) *ᵥ (exp ((t - k * options.Δt) • A) *ᵥ x 0
            + MatExp.expIntegral A (t - k * options.Δt) *ᵥ uc)
          + MatExp.expIntegral A ((k : ℝ) * options.Δt) *ᵥ uc)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - uc) := by
    rw [hsum, hconst, hexp, Matrix.mulVec_add]
    abel
  -- window `k`, and `k < N`
  refine SetUnion.mem_construct.mpr
    ⟨sys.aux_reachStepkInput options.Δt (m + 2) params.X₀ V k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hvoc, hx]
    refine Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _
      (Set.add_mem_add ?_ ?_)) ?_)
    · -- `e^{[A]t_k}` of a point of `(H^R ⊕ P̃^R)(τ_0)`
      refine Mtimes.mtimes_outer _ _ (Set.mem_biUnion (sys.exp_mem_expEnclosure _ (m + 2)
        traj.param) (Set.mem_image_of_mem _ (Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_))))
      · exact sys.timeIntervalStep_outer hΔt hε params.X₀ traj.param hτ0 htk
          (Set.mem_image_of_mem _ traj.init)
      · exact sys.expIntegral_mem_constInputSolution hΔt (m + 2) hε traj.param uc hτ0 htk
    · -- `P̃(t_k)`, at every step by `constPropagate`
      exact sys.expIntegral_mem_constPropagate hΔt (m + 2) hε traj.param uc k
    · -- one admissible `Ũ`-input's contribution by `t`, in `P^R_Ũ(t_{k+1})`
      exact sys.inputReach_subset_particularSolution hΔt hε traj.param
        (Recenter.zero_mem_recenter V) k ht.1 htk1
        ⟨fun s => u s - uc, hmem₀, hmeas₀, by simp only [Scalar.toRealMat_real]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
