module

public import CORALean.ContDynamics.NonlinearARX.Operations.FloatJacModelToNonlinearSysDTFloat
public import CORALean.ContDynamics.NonlinearARX.Theorems.FloatModelEnclosesToNonlinearSysDTFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

/-!
# The converted float model with Jacobians encloses the converted system

If `fm` encloses `f_ARX` with its Jacobians, `fm.toNonlinearSysDTFloat` encloses the field of
`toNonlinearSysDT` with its Jacobians: the value as for `FloatModel`, and the Jacobians because,
`f_ARX` being differentiable on the boxes, the converted field's Jacobian is the shift in the
first block rows and `f_ARX`'s Jacobian, reindexed newest first, in the last (the chain rule
through the reindexing, which is its own inverse).

## Inputs
* `fm` – float Jacobian model
* `sys` – ARX system

## Hypotheses
* `h` – the float model encloses the system

## Conclusion
* the converted float model with Jacobians encloses the converted system
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A Jacobian entry is the derivative of that component along that coordinate. -/
theorem aux_jacobianMat_apply_of_hasFDerivAt {k N : ℕ} (g : Vec ℝ k → Vec ℝ N) (x : Vec ℝ k)
    (D : Fin N → (Vec ℝ k →L[ℝ] ℝ)) (hg : ∀ i, HasFDerivAt (fun x => g x i) (D i) x)
    (i : Fin N) (j : Fin k) :
    jacobianMat g x i j = D i (Pi.single j 1) := by
  have h : HasFDerivAt g (ContinuousLinearMap.pi D) x := hasFDerivAt_pi.2 hg
  unfold jacobianMat
  rw [h.fderiv, LinearMap.toMatrix'_apply]
  rfl

/-- Reading `p` blocks newest first is its own inverse. -/
theorem aux_rev_rev {a b : ℕ} (c : Fin (a * b)) : -- --- CONCL ---
    finProdFinEquiv (Fin.rev (finProdFinEquiv.symm (finProdFinEquiv (Fin.rev
      (finProdFinEquiv.symm c).1, (finProdFinEquiv.symm c).2))).1,
      (finProdFinEquiv.symm (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm c).1,
        (finProdFinEquiv.symm c).2))).2) = c := by -- --- PROOF ---
  simp only [Equiv.symm_apply_apply, Fin.rev_rev, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The reindexing, as a continuous linear map, sends a unit vector to a unit vector. -/
theorem aux_reindex_hasFDerivAt {a b : ℕ} (x : Vec ℝ (a * b)) : -- --- CONCL ---
    ∃ L : Vec ℝ (a * b) →L[ℝ] Vec ℝ (a * b),
      HasFDerivAt (fun x' : Vec ℝ (a * b) => fun s => x' (finProdFinEquiv
        (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2))) L x ∧
      ∀ c, L (Pi.single c 1) = Pi.single (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm c).1,
        (finProdFinEquiv.symm c).2)) 1 := by -- --- PROOF ---
  refine ⟨ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (finProdFinEquiv
    (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2)), ?_, fun c => ?_⟩
  · exact hasFDerivAt_pi.2 fun s => hasFDerivAt_apply _ x
  · funext s
    simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · rintro rfl
      exact (aux_rev_rev s).symm
    · rintro rfl
      exact aux_rev_rev c


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.FloatJacModel.Encloses.toNonlinearSysDTFloat
    {fm : NonlinearARX.FloatJacModel 𝕋 dy du p} {sys : NonlinearARX dy du p}
    (h : fm.Encloses sys) : -- --- CONCL ---
    fm.toNonlinearSysDTFloat.Encloses sys.toNonlinearSysDT.f := by -- --- PROOF ---
  -- a vector is in a float box when every coordinate is between the real bounds
  have mem_iff : ∀ {k : ℕ} (I : Interval (Vec 𝕋 k)) (v : Vec ℝ k),
      v ∈ construct I ↔ ∀ i, toReal (I.inf i) ≤ v i ∧ v i ≤ toReal (I.sup i) :=
    fun _ _ => Iff.rfl
  -- the window and the inputs newest first lie in the reindexed boxes
  have hY : ∀ (X : Interval (Vec 𝕋 (p * dy))) (x : Vec ℝ (p * dy)), x ∈ construct X →
      (fun s => x (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2))) ∈ construct (⟨fun s => X.inf (finProdFinEquiv
            (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2)),
          fun s => X.sup (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
            (finProdFinEquiv.symm s).2))⟩ : Interval (Vec 𝕋 (p * dy))) :=
    fun X x hx => (mem_iff _ _).2 fun s => (mem_iff _ _).1 hx _
  have hW : ∀ (V : Interval (Vec 𝕋 ((p + 1) * du))) (v : Vec ℝ ((p + 1) * du)),
      v ∈ construct V →
      (fun s => v (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
          (finProdFinEquiv.symm s).2))) ∈ construct (⟨fun s => V.inf (finProdFinEquiv
            (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2)),
          fun s => V.sup (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
            (finProdFinEquiv.symm s).2))⟩ : Interval (Vec 𝕋 ((p + 1) * du))) :=
    fun V v hv => (mem_iff _ _).2 fun s => (mem_iff _ _).1 hv _
  refine ⟨(NonlinearARX.FloatModel.Encloses.toNonlinearSysDTFloat
    (fm := ⟨fm.f⟩) ⟨h.f_mem⟩).f_mem, fun X V x hx v hv => ?_, fun X V x hx v hv => ?_⟩
  · -- `∂/∂x`: the shift in the first block rows, `A_lin` reindexed in the last
    -- each row's derivative: a projection, zero, or `f_ARX`'s through the reindexing
    obtain ⟨L, hL, hL1⟩ := aux_reindex_hasFDerivAt x
    have hg := (h.differentiableY _ _ _ (hY X x hx) _ (hW V v hv)).hasFDerivAt
    let D : Fin (p * dy) → (Vec ℝ (p * dy) →L[ℝ] ℝ) := fun r =>
      if hr : (finProdFinEquiv.symm r).1.val + 1 < p then
        ContinuousLinearMap.proj (finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, hr⟩ :
          Fin p), (finProdFinEquiv.symm r).2))
      else (ContinuousLinearMap.proj (finProdFinEquiv.symm r).2).comp
        ((fderiv ℝ (fun y' => sys.f y' (fun s => v (finProdFinEquiv
          (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2))))
          (fun s => x (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
            (finProdFinEquiv.symm s).2)))).comp L)
    have hD : ∀ r, HasFDerivAt (fun x' => sys.toNonlinearSysDT.f x' v r) (D r) x := by
      intro r
      by_cases hr : (finProdFinEquiv.symm r).1.val + 1 < p
      · simp only [D, NonlinearARX.toNonlinearSysDT, dif_pos hr]
        exact hasFDerivAt_apply _ x
      · simp only [D, NonlinearARX.toNonlinearSysDT, dif_neg hr]
        exact (hasFDerivAt_apply _ _).comp x (hg.comp x hL)
    -- entrywise, the Jacobian is that derivative at a unit vector
    refine Interval.mem_mat_iff.2 fun r c => ?_
    rw [aux_jacobianMat_apply_of_hasFDerivAt _ x D hD]
    unfold NonlinearARX.FloatJacModel.toNonlinearSysDTFloat
    by_cases hr : (finProdFinEquiv.symm r).1.val + 1 < p
    · simp only [D, dif_pos hr, ContinuousLinearMap.proj_apply, Pi.single_apply]
      by_cases hc : c = finProdFinEquiv ((⟨(finProdFinEquiv.symm r).1.val + 1, hr⟩ : Fin p),
          (finProdFinEquiv.symm r).2)
      · rw [if_pos hc, if_pos hc.symm, toReal_one]
        exact ⟨le_rfl, le_rfl⟩
      · rw [if_neg hc, if_neg (Ne.symm hc), toReal_zero]
        exact ⟨le_rfl, le_rfl⟩
    · simp only [D, dif_neg hr, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        hL1]
      -- `f_ARX`'s Jacobian, at the reindexed column
      have hJ := Interval.mem_mat_iff.1
        (h.jacY_mem _ _ _ (hY X x hx) _ (hW V v hv)) (finProdFinEquiv.symm r).2
        (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm c).1, (finProdFinEquiv.symm c).2))
      rw [jacobianMat, LinearMap.toMatrix'_apply] at hJ
      exact hJ
  · -- `∂/∂u`: zero in the first block rows, `B_lin` reindexed in the last
    -- each row's derivative: a projection, zero, or `f_ARX`'s through the reindexing
    obtain ⟨L, hL, hL1⟩ := aux_reindex_hasFDerivAt v
    have hg := (h.differentiableU _ _ _ (hY X x hx) _ (hW V v hv)).hasFDerivAt
    let D : Fin (p * dy) → (Vec ℝ ((p + 1) * du) →L[ℝ] ℝ) := fun r =>
      if (finProdFinEquiv.symm r).1.val + 1 < p then 0
      else (ContinuousLinearMap.proj (finProdFinEquiv.symm r).2).comp
        ((fderiv ℝ (fun v' => sys.f (fun s => x (finProdFinEquiv
          (Fin.rev (finProdFinEquiv.symm s).1, (finProdFinEquiv.symm s).2))) v')
          (fun s => v (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm s).1,
            (finProdFinEquiv.symm s).2)))).comp L)
    have hD : ∀ r, HasFDerivAt (fun v' => sys.toNonlinearSysDT.f x v' r) (D r) v := by
      intro r
      by_cases hr : (finProdFinEquiv.symm r).1.val + 1 < p
      · simp only [D, NonlinearARX.toNonlinearSysDT, dif_pos hr, if_pos hr]
        exact hasFDerivAt_const _ _
      · simp only [D, NonlinearARX.toNonlinearSysDT, dif_neg hr, if_neg hr]
        exact (hasFDerivAt_apply _ _).comp v (hg.comp v hL)
    -- entrywise, the Jacobian is that derivative at a unit vector
    refine Interval.mem_mat_iff.2 fun r c => ?_
    rw [aux_jacobianMat_apply_of_hasFDerivAt _ v D hD]
    unfold NonlinearARX.FloatJacModel.toNonlinearSysDTFloat
    by_cases hr : (finProdFinEquiv.symm r).1.val + 1 < p
    · simp only [D, if_pos hr]
      simp [toReal_zero]
    · simp only [D, if_neg hr, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        hL1]
      -- `f_ARX`'s Jacobian, at the reindexed column
      have hJ := Interval.mem_mat_iff.1
        (h.jacU_mem _ _ _ (hY X x hx) _ (hW V v hv)) (finProdFinEquiv.symm r).2
        (finProdFinEquiv (Fin.rev (finProdFinEquiv.symm c).1, (finProdFinEquiv.symm c).2))
      rw [jacobianMat, LinearMap.toMatrix'_apply] at hJ
      exact hJ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
