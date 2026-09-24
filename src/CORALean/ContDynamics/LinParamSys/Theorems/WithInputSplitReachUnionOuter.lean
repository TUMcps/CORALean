import CORALean.ContDynamics.LinParamSys.Definitions.WithInputSplitReachUnionExact
import CORALean.ContDynamics.LinParamSys.Operations.WithInputSplitReachUnion
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstInputSolution
import CORALean.ContDynamics.LinParamSys.Theorems.ExpIntegralMemConstPropagate
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolution
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindow
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralAddMulVec
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralConstInput
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.IntervalIntegrableExpSubMulVec
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# `reachUnion` with the input set split encloses every constant-parameter run

[1, Alg. 4]'s soundness, the input set anywhere. A run fixes one member `A`,
and is the point system `⟨A⟩`'s run (`toLinearSys`), so at `t` it is at
`e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds`; with `u = ũ + (u - ũ)` the integral is
`∫₀ᵗ e^{Aσ}dσ ũ` plus one admissible `Ũ`-input's contribution, and with
`t = t_k + τ` both the free motion and the constant's part are `e^{A t_k}` of
their values at `τ`, the constant's plus `P̃(t_k)` (`expIntegral_add_mulVec`).
At `τ ∈ [0, Δt]` those are in `H^R(τ_0)` and `P̃^R(τ_0)`, `P̃(t_k)` is
`expIntegral_mem_constPropagate`, and the `Ũ` part is in `P^R_Ũ(t_{k+1})`,
`0 ∈ Ũ` being `Recentre`'s.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [∀ n, OfPoint (S n) (Vec ℝ n)] [∀ n, Recentre (S n) (Vec ℝ n)] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

-- the window's four summands, each elaborating a `Mtimes` instance at `ℐ`
set_option maxHeartbeats 1000000 in
/-- Every state a constant-parameter run on `[0, p.tFinal]` from `X₀`, under
inputs in `sys.U` wherever it sits, reaches is in one of `reachUnion`'s
windows. -/
theorem LinParamSys.WithInputSplit.reachUnion_outer (sys : LinParamSys.WithInputSplit S n)
    (p : LinearSys.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  rintro _ ⟨A, x, u, traj, t, ht, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window p.hΔt ht
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * p.Δt := by push_cast; linarith
  have hτ0 : 0 ≤ t - k * p.Δt := sub_nonneg.mpr hkt
  have htk0 : 0 ≤ (k : ℝ) * p.Δt := mul_nonneg (Nat.cast_nonneg k) p.hΔt.le
  -- the order `reachUnion` runs at, `m + 2` in `reachStepk_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max p.η (sys.sys.reachOrder p.Δt + 2) = m + 2 :=
    ⟨max p.η (sys.sys.reachOrder p.Δt + 2) - 2, by omega⟩
  have hε : ‖(Interval.smul p.Δt sys.sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    have hadm := sys.sys.reachOrder_admissible p.Δt
    have hle : ((sys.sys.reachOrder p.Δt + 2 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast hm ▸ le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) hadm
  set uc := Recentre.centre sys.U with huc
  -- the run is the point system `⟨A⟩`'s, split into its free motion and its input's integral
  have trajL := traj.toLinearSys
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 p.tFinal := Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct (construct sys.U)) :=
    CompactSet.isBounded_construct sys.U
  have hvoc := trajL.variation_of_constants hTt ht.1 (trajL.intervalIntegrable_input hTt ht.1 hU)
  simp only [sub_zero, Scalar.toRealMat_real] at hvoc
  -- the input, split along `U ⊆ {ũ} ⊞ Ũ`
  have hmem₀ : ∀ s ∈ Set.Icc (0:ℝ) t, u s - uc ∈ construct (Recentre.recentre sys.U) :=
    fun s hs => Recentre.sub_centre_mem_recentre (traj.input s (hTt hs))
  have hmeas₀ : AEStronglyMeasurable (fun s => u s - uc) (volume.restrict (Set.Icc 0 t)) :=
    (trajL.aestronglyMeasurable_input hTt).sub aestronglyMeasurable_const
  have hint₁ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (OfPoint.ofPoint uc : S n))
    (fun _ _ => OfPoint.mem_ofPoint uc) aestronglyMeasurable_const
  have hint₀ := intervalIntegrable_expSub_mulVec (A := A) (c := t) ht.1
    (CompactSet.isBounded_construct (Recentre.recentre sys.U)) hmem₀ hmeas₀
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
      = exp (((k : ℝ) * p.Δt) • A) *ᵥ (MatExp.expIntegral A (t - k * p.Δt) *ᵥ uc)
        + MatExp.expIntegral A ((k : ℝ) * p.Δt) *ᵥ uc := by
    rw [MatExp.expIntegral_constInput A uc ht.1]
    have h := MatExp.expIntegral_add_mulVec A uc hτ0 htk0
    rwa [sub_add_cancel] at h
  -- `e^{At} = e^{A t_k} e^{Aτ}`, both powers of the same member
  have hexp : exp (t • A) *ᵥ x 0
      = exp (((k : ℝ) * p.Δt) • A) *ᵥ (exp ((t - k * p.Δt) • A) *ᵥ x 0) := by
    have hc : Commute (((k : ℝ) * p.Δt) • A) ((t - k * p.Δt) • A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x 0) h
  -- regrouped as the window's summands
  have hx : exp (t • A) *ᵥ x 0 + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s
      = (exp (((k : ℝ) * p.Δt) • A) *ᵥ (exp ((t - k * p.Δt) • A) *ᵥ x 0
            + MatExp.expIntegral A (t - k * p.Δt) *ᵥ uc)
          + MatExp.expIntegral A ((k : ℝ) * p.Δt) *ᵥ uc)
        + ∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ (u s - uc) := by
    rw [hsum, hconst, hexp, Matrix.mulVec_add]
    abel
  -- window `k`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk p.Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hvoc, hx]
    refine Plus.plus_outer _ _ (Set.add_mem_add (Plus.plus_outer _ _
      (Set.add_mem_add ?_ ?_)) ?_)
    · -- `e^{[A]t_k}` of a point of `(H^R ⊕ P̃^R)(τ_0)`
      refine Mtimes.mtimes_outer _ _ (Set.mem_biUnion (sys.sys.exp_mem_expEnclosure _ (m + 2)
        traj.param) (Set.mem_image_of_mem _ (Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_))))
      · exact sys.sys.timeIntervalStep_outer p.hΔt hε X₀ traj.param hτ0 htk
          (Set.mem_image_of_mem _ traj.init)
      · exact sys.sys.expIntegral_mem_constInputSolution p.hΔt (m + 2) hε traj.param uc hτ0 htk
    · -- `P̃(t_k)`, at every step by `constPropagate`
      exact sys.sys.expIntegral_mem_constPropagate p.hΔt (m + 2) hε traj.param uc k
    · -- one admissible `Ũ`-input's contribution by `t`, in `P^R_Ũ(t_{k+1})`
      exact sys.sys.inputReach_subset_particularSolution p.hΔt hε traj.param
        (Recentre.zero_mem_recentre sys.U) k ht.1 htk1
        ⟨fun s => u s - uc, hmem₀, hmeas₀, by simp only [Scalar.toRealMat_real]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
