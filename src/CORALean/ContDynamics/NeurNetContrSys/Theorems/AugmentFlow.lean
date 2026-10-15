module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.JoinInputInj
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.MulVecJoinInput
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CORALean.ContDynamics.NeurNetContrSys.Definitions.IsTrajectory
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic

@[expose] public section

/-!
# At a linear plant, a control period is a run of the augmented system

CORA's `aux_augmentLinear`, checked: a run of the plant `ẋ = A x + B u + c + E w` on `[0, τ]`
under the input `[a; v(t)]`, the network's held output `a` and an external input `v` in `U_ext`,
with a disturbance `E` sends to `0`, is with `a` appended to it a Carathéodory run of `augment`,
`ż = [A B_nn; 0 0] z + [B_ext; 0] v + [c; 0]` (`aux_augment_mulVec_append`). This is what lets
`LinearSys`'s own reachability reach a control period of the closed loop, the external input
entering as `B_aug v ∈ B_aug U_ext`. `U_ext` is bounded, which makes `B_ext v` integrable: `v` is
measurable only. CORA's loop drops `E` instead; the hypothesis on the disturbance is what makes
that sound.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `augment`'s field at `[x; a]` under the external input `e` is the plant's,
`A x + B_nn a + B_ext e + c`, over a zero input part. -/
theorem NeurNetContrSys.aux_augment_mulVec_append (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (x : Vec ℝ n) (a : Vec ℝ sys.m) (e : Vec ℝ sys.nExt) :
    sys.augment.A *ᵥ (Fin.append x a : Vec ℝ (n + sys.m)) + (sys.augment.B *ᵥ e + sys.augment.c) =
      Fin.append (toRealMat sys.plant.A *ᵥ x + leftCols sys.hm (toRealMat sys.plant.B) *ᵥ a +
        rightCols sys.hm (toRealMat sys.plant.B) *ᵥ e + toRealVec sys.plant.c)
        (0 : Vec ℝ sys.m) := by -- --- PROOF ---
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [NeurNetContrSys.augment, Matrix.mulVec, dotProduct, Fin.sum_univ_add, add_assoc]
    rfl
  · simp [NeurNetContrSys.augment, Matrix.mulVec, dotProduct, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the linear plant on `[0, τ]` under the input `[a; v(t)]`, `v` in a bounded `U_ext`
and its disturbance in a `W` that `E` sends to `0`, is with `a` appended a continuous solution of
`augment`'s integral equation under the input `v`, its input `B_aug v + c_aug` measurable. -/
theorem NeurNetContrSys.augment_flow (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) {τ : ℝ}
    {U_ext : Set (Vec ℝ sys.nExt)} (hU : Bornology.IsBounded U_ext)
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {a : Vec ℝ sys.m} {v : ℝ → Vec ℝ sys.nExt} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : ContDynamics.IsTrajectory sys.plant (Set.Icc 0 τ) Set.univ (sys.inputSet {a} U_ext) W x
      (fun t => sys.input a (v t)) w) :
    ContinuousOn (fun t => (Fin.append (x t) a : Vec ℝ (n + sys.m))) (Set.Icc 0 τ) ∧
      (∀ t ∈ Set.Icc 0 τ, v t ∈ U_ext) ∧
      MeasureTheory.AEStronglyMeasurable (fun t => sys.augment.B *ᵥ v t + sys.augment.c)
        (MeasureTheory.volume.restrict (Set.Icc 0 τ)) ∧
      ∀ t ∈ Set.Icc 0 τ, (Fin.append (x t) a : Vec ℝ (n + sys.m)) =
        Fin.append (x 0) a + ∫ s in (0:ℝ)..t,
          (sys.augment.A *ᵥ (Fin.append (x s) a : Vec ℝ (n + sys.m)) +
            (sys.augment.B *ᵥ v s + sys.augment.c)) := by -- --- PROOF ---
  obtain ⟨vv, y, tr⟩ := traj
  -- the external input lies in `U_ext`
  have hv : ∀ t ∈ Set.Icc 0 τ, v t ∈ U_ext := by
    intro t ht
    obtain ⟨a', _, e, he, heq⟩ := tr.input t ht
    have := (joinInput_inj sys.hm heq).2
    rw [this]
    exact he
  -- and is measurable: it is a coordinate block of the plant's input
  have hvm : MeasureTheory.AEStronglyMeasurable v
      (MeasureTheory.volume.restrict (Set.Icc 0 τ)) := by
    have hproj : v = fun t => (fun u : Vec ℝ sys.plant.m => fun j : Fin sys.nExt =>
        u ⟨sys.m + j.val, by
          have h1 : j.val < ContDynamics.nrOfInputs sys.plant - sys.m := j.isLt
          have h2 : ContDynamics.nrOfInputs sys.plant = sys.plant.m := rfl
          have h3 := sys.hm
          omega⟩) (sys.input a (v t)) := by
      funext t j
      simp [NeurNetContrSys.input, joinInput]
    rw [hproj]
    exact (continuous_pi fun j => continuous_apply _).comp_aestronglyMeasurable tr.meas
  -- the state part is continuous, the input part constant
  have hcont : ContinuousOn (fun t => (Fin.append (x t) a : Vec ℝ (n + sys.m)))
      (Set.Icc 0 τ) := by
    refine continuousOn_pi.2 fun k => ?_
    refine Fin.addCases (fun e => ?_) (fun j => ?_) k
    · simpa [Fin.append_left] using continuousOn_pi.1 tr.cont e
    · simpa [Fin.append_right] using continuousOn_const
  -- `B_ext v` is bounded and measurable, so integrable
  have hcm : Continuous (fun y : Vec ℝ sys.nExt =>
      rightCols sys.hm (toRealMat sys.plant.B) *ᵥ y) := continuous_const.matrix_mulVec continuous_id
  obtain ⟨C, hC⟩ := hU.exists_norm_le
  have hFe : MeasureTheory.IntegrableOn
      (fun s => rightCols sys.hm (toRealMat sys.plant.B) *ᵥ v s) (Set.Icc 0 τ) := by
    refine ⟨hcm.comp_aestronglyMeasurable hvm,
      MeasureTheory.HasFiniteIntegral.of_bounded
        (C := ‖rightCols sys.hm (toRealMat sys.plant.B)‖ * C) ?_⟩
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun s hs => ?_
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul_of_nonneg_left (hC _ (hv s hs)) (norm_nonneg _))
  -- the plant's field without `B_ext v`, continuous on the period
  set F₁ : ℝ → Vec ℝ n := fun s =>
    toRealMat sys.plant.A *ᵥ x s + leftCols sys.hm (toRealMat sys.plant.B) *ᵥ a +
      toRealVec sys.plant.c with hF₁
  have hF₁c : ContinuousOn F₁ (Set.Icc 0 τ) :=
    (((continuous_const.matrix_mulVec continuous_id).comp_continuousOn tr.cont).add
      continuousOn_const).add continuousOn_const
  set F : ℝ → Vec ℝ n := fun s => F₁ s + rightCols sys.hm (toRealMat sys.plant.B) *ᵥ v s with hF
  have hFi : MeasureTheory.IntegrableOn F (Set.Icc 0 τ) :=
    hF₁c.integrableOn_Icc.add hFe
  refine ⟨hcont, hv, ?_, fun t ht => ?_⟩
  · have hcm' : Continuous (fun y : Vec ℝ sys.nExt => sys.augment.B *ᵥ y + sys.augment.c) :=
      (continuous_const.matrix_mulVec continuous_id).add continuous_const
    exact hcm'.comp_aestronglyMeasurable hvm
  have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 τ := by
    rw [Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc le_rfl ht.2
  -- on `[0, t]` the disturbance is in `W`, so `E w` drops out of the plant's integral
  have hflow : x t = x 0 + ∫ s in (0:ℝ)..t, F s := by
    rw [tr.flow t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hF, hF₁, hW _ (tr.dist s (hsub hs)), add_zero]
    rw [show sys.input a (v s) = joinInput sys.hm a (v s) from rfl, mulVec_joinInput]
    abel
  -- the augmented integrand is the plant's, over a zero input part: `L` appends the zeros
  let L : Vec ℝ n →L[ℝ] Vec ℝ (n + sys.m) := LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.append y (0 : Vec ℝ sys.m)
      map_add' := fun y z => by
        funext k; refine Fin.addCases (fun e => ?_) (fun j => ?_) k <;> simp
      map_smul' := fun c y => by
        funext k; refine Fin.addCases (fun e => ?_) (fun j => ?_) k <;> simp }
  have hL : ∀ y, L y = Fin.append y (0 : Vec ℝ sys.m) := fun y => rfl
  -- `L` commutes with the integral, which turns the augmented integrand into `L (∫ F)`
  have hint : IntervalIntegrable F MeasureTheory.volume 0 t :=
    (hFi.mono_set hsub).intervalIntegrable
  have hcomm := L.intervalIntegral_comp_comm hint
  have hG : ∀ s, sys.augment.A *ᵥ (Fin.append (x s) a : Vec ℝ (n + sys.m)) +
      (sys.augment.B *ᵥ v s + sys.augment.c) = L (F s) := fun s => by
    rw [sys.aux_augment_mulVec_append, hL]
    congr 1
    simp only [hF, hF₁]
    abel
  simp only [hG]
  rw [hcomm, hL, hflow]
  funext k
  refine Fin.addCases (fun e => ?_) (fun j => ?_) k <;> simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
