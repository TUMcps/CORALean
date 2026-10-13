import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGO
import CORALean.ContDynamics.NonlinearARX.Operations.ComputeGOFloat
import CORALean.ContDynamics.NonlinearARX.Theorems.FloatJacModelEnclosesToNonlinearSysDTFloat
import CORALean.ContDynamics.NonlinearSysDT.Theorems.ComputeGOFloatOuter
import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
import CORALean.Global.JacobianMatAffine

/-!
# The float GO parameters of a nonlinear ARX model enclose the real ones

For a float model of `f_ARX` that encloses it with its Jacobians, everything `computeGO` returns
from the real value of a float start window under the real value of a float reference input
lies in what `computeGOFloat` returns: the reference run `x`, `y` and the parameters `A`, `B`,
`F`, `C`, `D`, `E`. `NonlinearSysDT.computeGOFloat_outer` at the converted model, whose
enclosure is `FloatJacModel.Encloses.toNonlinearSysDTFloat`, and at the selection matrix, whose
Jacobians are itself and zero. An outer statement; with `computeGO_output` it encloses the
output deviation of every run, the linearization errors `L_j` aside.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearARX.computeGOFloat_outer (sys : NonlinearARX dy du p)
    {fm : NonlinearARX.FloatJacModel 𝕋 dy du p} (h : fm.Encloses sys) (x0 : Vec 𝕋 (p * dy))
    (u_ref : ℕ → Vec 𝕋 du) (k j : ℕ) :
    let G := sys.computeGO (toRealVec x0) (fun i => toRealVec (u_ref i))
    let F := sys.computeGOFloat fm x0 u_ref
    G.x k ∈ (F.x k).construct ∧ G.y k ∈ (F.y k).construct ∧ G.A k ∈ (F.A k).construct ∧
      G.B k j ∈ (F.B k j).construct ∧ G.F k j ∈ (F.F k j).construct ∧
      G.C k ∈ (F.C k).construct ∧ G.D k j ∈ (F.D k j).construct ∧
      G.E k j ∈ (F.E k j).construct := by -- --- PROOF ---
  intro G F
  -- the stored selection matrix reads as the real one
  have hC : toRealMat (sys.outputSel (𝕋 := 𝕋)) = sys.outputSel (𝕋 := ℝ) := by
    funext r c
    simp only [toRealMat, NonlinearARX.outputSel, Matrix.of_apply]
    split_ifs
    · exact toReal_one
    · exact toReal_zero
  -- the selection, its value by `mtimes` and its Jacobians, encloses the output equation
  have ho : NonlinearSysDT.FloatJacModel.Encloses
      (⟨fun X _ => Interval.mtimes (sys.outputSel (𝕋 := 𝕋)) X,
        fun _ _ => Interval.point (sys.outputSel (𝕋 := 𝕋)),
        fun _ _ => Interval.point fun _ _ => zero⟩ :
        NonlinearSysDT.FloatJacModel 𝕋 (p * dy) ((p + 1) * du) dy)
      (fun x (_ : Vec ℝ ((p + 1) * du)) => sys.outputSel (𝕋 := ℝ) *ᵥ x) := by
    refine ⟨fun X _ x hx _ _ => ?_, fun X _ x _ u _ => ?_, fun X _ x _ u _ => ?_⟩
    · rw [← hC]
      exact Interval.mtimes_outer _ X ⟨x, hx, rfl⟩
    · -- `∂/∂x` is the selection itself
      have hj : jacobianMat (fun x' => sys.outputSel (𝕋 := ℝ) *ᵥ x') x
          = sys.outputSel (𝕋 := ℝ) := by
        simpa using jacobianMat_affine 0 (sys.outputSel (𝕋 := ℝ)) x
      show jacobianMat (fun x' => sys.outputSel (𝕋 := ℝ) *ᵥ x') x ∈
        (Interval.point (sys.outputSel (𝕋 := 𝕋))).construct
      rw [hj, ← hC]
      exact Interval.mem_point _
    · -- `∂/∂u` is zero
      have hj : jacobianMat (fun (_ : Vec ℝ ((p + 1) * du)) => sys.outputSel (𝕋 := ℝ) *ᵥ x) u
          = 0 := by
        simpa using jacobianMat_affine (sys.outputSel (𝕋 := ℝ) *ᵥ x) 0 u
      have hz : toRealMat (show Mat 𝕋 dy ((p + 1) * du) from fun _ _ => zero) = 0 := by
        funext i l
        exact toReal_zero
      show jacobianMat (fun (_ : Vec ℝ ((p + 1) * du)) => sys.outputSel (𝕋 := ℝ) *ᵥ x) u ∈
        (Interval.point (show Mat 𝕋 dy ((p + 1) * du) from fun _ _ => zero)).construct
      rw [hj, ← hz]
      exact Interval.mem_point _
  -- the system case, at the converted model and the selection
  exact NonlinearSysDT.computeGOFloat_outer sys.toNonlinearSysDT _ h.toNonlinearSysDTFloat ho x0
    (NonlinearARX.feedFloat p u_ref) k j

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
