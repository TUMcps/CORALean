import CORALean.ContSet.Ellipsoid.Float.Operations.Project
import CORALean.ContSet.Ellipsoid.Real.Theorems.ProjectExact
import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
import CORALean.ContSet.Interval.Float.Theorems.ProjectOuter

/-!
# `Ellipsoid.project` over-approximates the projection

Selecting coordinates is linear and rounds nothing, so `InflatedContSet.image_subset` splits
this into the nominal ellipsoid and the box. The exact layer states `project` as `mtimes` at
the selection matrix, so the nominal ellipsoid of the projection has to be shown to be that
product, which is `aux_nominal_project`; after it `project_exact` gives the nominal obligation
as an equality, and the box is `Interval.project_outer`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The selection matrix times a stored matrix reads the stored rows. -/
theorem Ellipsoid.aux_nominal_project (E : Ellipsoid 𝕋 n) (dims : Fin m → Fin n) :
    nominal (E.project dims) = Real.Ellipsoid.project (nominal E) dims := by -- --- PROOF ---
  have hM : ∀ i k, LinearMap.toMatrix' (LinearMap.funLeft ℝ ℝ dims) i k
      = if dims i = k then (1 : ℝ) else 0 := by
    intro i k
    rw [LinearMap.toMatrix'_apply]
    simp [LinearMap.funLeft, Pi.single_apply, eq_comm]
  show Real.Ellipsoid.mk _ _ _ = Real.Ellipsoid.mk _ _ _
  congr 1
  · funext i
    simp [Matrix.mulVec, dotProduct, hM, toRealVec]
    rfl
  · funext i j
    simp [Matrix.mul_apply, hM, toRealMat]
    rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.project_outer (E : Ellipsoid 𝕋 n) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' E.construct ⊆ (E.project dims).construct :=
  image_subset (fun _ _ => rfl)
    (le_of_eq (by
      have h := Real.Ellipsoid.project_exact (nominal E) dims
      rw [← Ellipsoid.aux_nominal_project] at h
      exact h))
    (Interval.project_outer E.err dims)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
