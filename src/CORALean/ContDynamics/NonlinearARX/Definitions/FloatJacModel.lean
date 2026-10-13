import CORALean.ContDynamics.NonlinearARX.NonlinearARX
import CORALean.ContSet.Interval.Float.Instances
import CORALean.Global.Jacobian

/-!
# What a float run is told about a nonlinear ARX model and its Jacobians

`computeGO` linearizes `f_ARX` along the reference run (CORA's `nlnARX.jacobian`), by real
Jacobians (`jacobianMat`), which no float run can evaluate. A `FloatJacModel` is what it
evaluates instead: interval extensions of `f_ARX` and of its Jacobian blocks in the past outputs
and in the stacked inputs, over a box of each, as computable functions at the scalar `𝕋`.
`Encloses` ties it to `f_ARX`: the value, the Jacobians at every point of the boxes, and that
`f_ARX` is differentiable there, which the converted system's Jacobian is assembled from.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {dy du p : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- Interval extensions of `f_ARX` and of its Jacobian blocks `∂f/∂y`, `∂f/∂u`. -/
structure NonlinearARX.FloatJacModel (𝕋 : Type) (dy du p : ℕ) where
  f : Interval (Vec 𝕋 (p * dy)) → Interval (Vec 𝕋 ((p + 1) * du)) → Interval (Vec 𝕋 dy)
  jacY : Interval (Vec 𝕋 (p * dy)) → Interval (Vec 𝕋 ((p + 1) * du)) →
    Interval (Mat 𝕋 dy (p * dy))
  jacU : Interval (Vec 𝕋 (p * dy)) → Interval (Vec 𝕋 ((p + 1) * du)) →
    Interval (Mat 𝕋 dy ((p + 1) * du))

/-- `fm` encloses `sys` over every pair of boxes: `f_ARX` is differentiable there, and its value
and Jacobian blocks at every point lie in the extensions. A user-supplied hypothesis. -/
structure NonlinearARX.FloatJacModel.Encloses (fm : NonlinearARX.FloatJacModel 𝕋 dy du p)
    (sys : NonlinearARX dy du p) : Prop where
  f_mem (Y : Interval (Vec 𝕋 (p * dy))) (V : Interval (Vec 𝕋 ((p + 1) * du))) :
    ∀ y ∈ construct Y, ∀ v ∈ construct V, sys.f y v ∈ construct (fm.f Y V)
  differentiableY (Y : Interval (Vec 𝕋 (p * dy))) (V : Interval (Vec 𝕋 ((p + 1) * du))) :
    ∀ y ∈ construct Y, ∀ v ∈ construct V, DifferentiableAt ℝ (fun y' => sys.f y' v) y
  differentiableU (Y : Interval (Vec 𝕋 (p * dy))) (V : Interval (Vec 𝕋 ((p + 1) * du))) :
    ∀ y ∈ construct Y, ∀ v ∈ construct V, DifferentiableAt ℝ (fun v' => sys.f y v') v
  jacY_mem (Y : Interval (Vec 𝕋 (p * dy))) (V : Interval (Vec 𝕋 ((p + 1) * du))) :
    ∀ y ∈ construct Y, ∀ v ∈ construct V,
      jacobianMat (fun y' => sys.f y' v) y ∈ construct (fm.jacY Y V)
  jacU_mem (Y : Interval (Vec 𝕋 (p * dy))) (V : Interval (Vec 𝕋 ((p + 1) * du))) :
    ∀ y ∈ construct Y, ∀ v ∈ construct V,
      jacobianMat (fun v' => sys.f y v') v ∈ construct (fm.jacU Y V)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
