module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# At a linear plant, a control period is a run of the augmented system

CORA's `aux_augmentLinear`, checked: a run of the plant `ẋ = A x + B u + c + E w` on `[0, τ]`
under a held input `u`, with a disturbance `E` sends to `0`, is with `u` appended to it a
Carathéodory run of `augment`, `ż = [A B; 0 0] z + [c; 0]`, the field of the plant at `z = [x; u]`
(`aux_augment_mulVec_append`). This is what lets `LinearSys`'s own reachability reach a control
period of the closed loop. CORA's loop drops `E` instead; the hypothesis on the disturbance is
what makes that sound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `augment`'s field at `[x; u]` is the plant's, `A x + B u + c`, over a zero input part. -/
theorem NeurNetContrSys.aux_augment_mulVec_append (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (x : Vec ℝ n) (u : Vec ℝ sys.plant.m) :
    sys.augment.A *ᵥ (Fin.append x u : Vec ℝ (n + sys.plant.m)) + sys.augment.c =
      Fin.append (toRealMat sys.plant.A *ᵥ x + toRealMat sys.plant.B *ᵥ u + toRealVec sys.plant.c)
        (0 : Vec ℝ sys.plant.m) := by -- --- PROOF ---
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp [NeurNetContrSys.augment, Matrix.mulVec, dotProduct, Fin.sum_univ_add, add_assoc]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A run of the linear plant on `[0, τ]` under the held input `u`, its disturbance in a `W` that
`E` sends to `0`, is with `u` appended a continuous solution of `augment`'s integral equation. -/
theorem NeurNetContrSys.augment_flow (sys : NeurNetContrSys (LinearSys 𝕋 n) S n) {τ : ℝ}
    {W : Set (Vec ℝ sys.plant.r)} (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0)
    {x : ℝ → Vec ℝ n} {u : Vec ℝ sys.plant.m} {w : ℝ → Vec ℝ sys.plant.r}
    (traj : ContDynamics.Trajectory sys.plant (Set.Icc 0 τ) Set.univ Set.univ W x (fun _ => u)
      w) :
    ContinuousOn (fun t => (Fin.append (x t) u : Vec ℝ (n + sys.plant.m))) (Set.Icc 0 τ) ∧
      ∀ t ∈ Set.Icc 0 τ, (Fin.append (x t) u : Vec ℝ (n + sys.plant.m)) =
        Fin.append (x 0) u + ∫ s in (0:ℝ)..t,
          (sys.augment.A *ᵥ (Fin.append (x s) u : Vec ℝ (n + sys.plant.m)) +
            sys.augment.c) := by -- --- PROOF ---
  obtain ⟨v, y, tr⟩ := traj
  -- the state part is continuous, the input part constant
  have hcont : ContinuousOn (fun t => (Fin.append (x t) u : Vec ℝ (n + sys.plant.m)))
      (Set.Icc 0 τ) := by
    refine continuousOn_pi.2 fun k => ?_
    refine Fin.addCases (fun e => ?_) (fun j => ?_) k
    · simpa [Fin.append_left] using continuousOn_pi.1 tr.cont e
    · simpa [Fin.append_right] using continuousOn_const
  refine ⟨hcont, fun t ht => ?_⟩
  have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 τ := by
    rw [Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc le_rfl ht.2
  -- the plant's field, continuous on the period
  set F : ℝ → Vec ℝ n := fun s =>
    toRealMat sys.plant.A *ᵥ x s + toRealMat sys.plant.B *ᵥ u + toRealVec sys.plant.c with hF
  have hFc : ContinuousOn F (Set.Icc 0 τ) :=
    (((continuous_const.matrix_mulVec continuous_id).comp_continuousOn tr.cont).add
      continuousOn_const).add continuousOn_const
  -- on `[0, t]` the disturbance is in `W`, so `E w` drops out of the plant's integral
  have hflow : x t = x 0 + ∫ s in (0:ℝ)..t, F s := by
    rw [tr.flow t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hF, hW _ (tr.dist s (hsub hs)), add_zero]
  -- the augmented integrand, coordinate by coordinate
  set G : ℝ → Vec ℝ (n + sys.plant.m) := fun s =>
    sys.augment.A *ᵥ (Fin.append (x s) u : Vec ℝ (n + sys.plant.m)) + sys.augment.c with hG
  have hGF : ∀ s, G s = Fin.append (F s) (0 : Vec ℝ sys.plant.m) := fun s =>
    sys.aux_augment_mulVec_append (x s) u
  have hGc : ContinuousOn G (Set.Icc 0 τ) := by
    refine continuousOn_pi.2 fun k => ?_
    refine Fin.addCases (fun e => ?_) (fun j => ?_) k
    · simpa [hGF, Fin.append_left] using continuousOn_pi.1 hFc e
    · simpa [hGF, Fin.append_right] using continuousOn_const
  have hGi : IntervalIntegrable G MeasureTheory.volume 0 t := (hGc.mono hsub).intervalIntegrable
  have hFi : IntervalIntegrable F MeasureTheory.volume 0 t := (hFc.mono hsub).intervalIntegrable
  have hGk : ∀ k, (∫ s in (0:ℝ)..t, G s) k = ∫ s in (0:ℝ)..t, G s k := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + sys.plant.m) => ℝ) k)
      |>.intervalIntegral_comp_comm hGi).symm
  have hFk : ∀ e, (∫ s in (0:ℝ)..t, F s) e = ∫ s in (0:ℝ)..t, F s e := fun e =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) e)
      |>.intervalIntegral_comp_comm hFi).symm
  show _ = Fin.append (x 0) u + ∫ s in (0:ℝ)..t, G s
  funext k
  refine Fin.addCases (fun e => ?_) (fun j => ?_) k
  · -- the state: the plant's own equation
    rw [Pi.add_apply, hGk, Fin.append_left, Fin.append_left, hflow, Pi.add_apply, hFk]
    simp [hGF, Fin.append_left]
  · -- the held input: constant, its field zero
    rw [Pi.add_apply, hGk]
    simp [hGF, Fin.append_right]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
