module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# The area formula on the factor cube, for a matrix derivative

The two halves of Mathlib's change of variables on `[-1,1]ᵖ` for a map whose derivative at `a` is
the matrix `M a`, with `det ≥ 0` there: the image's volume is at most `∫ det`, and equal to it
if the map is injective on the cube.

## Inputs
* `p` – number of factors
* `f` – map of the factor cube
* `M` – matrix derivative of the map

## Hypotheses
* `hf` – the matrix is the derivative
* `hM` – the matrix is continuous
* `hdet` – determinant is nonnegative on the cube

## Conclusion
* volume of the image is bounded by the integral of the determinant
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open MeasureTheory


-- =======================================  MAIN THEOREM  ======================================= --

/-- The area formula for a map whose derivative is the matrix `M a`, on the factor cube. -/
theorem PolyZonotope.area_formula {p : ℕ} (f : (Fin p → ℝ) → (Fin p → ℝ))
    (M : (Fin p → ℝ) → Matrix (Fin p) (Fin p) ℝ)
    (hf : ∀ a, HasFDerivAt f (LinearMap.toContinuousLinearMap (Matrix.toLin' (M a))) a)
    (hM : Continuous M)
    (hdet : ∀ a ∈ Set.Icc (fun _ : Fin p => (-1 : ℝ)) (fun _ => 1),
      0 ≤ (M a).det) : -- --- CONCL ---
    MeasureTheory.volume (f '' Set.Icc (fun _ : Fin p => (-1 : ℝ)) (fun _ => 1))
        ≤ ENNReal.ofReal (∫ a in Set.Icc (fun _ : Fin p => (-1 : ℝ)) (fun _ => 1), (M a).det)
      ∧ (Set.InjOn f (Set.Icc (fun _ : Fin p => (-1 : ℝ)) (fun _ => 1)) →
        MeasureTheory.volume (f '' Set.Icc (fun _ : Fin p => (-1 : ℝ)) (fun _ => 1))
          = ENNReal.ofReal (∫ a in Set.Icc (fun _ : Fin p => (-1 : ℝ)) (fun _ => 1),
              (M a).det)) := by -- --- PROOF ---
  set s : Set (Fin p → ℝ) := Set.Icc (fun _ => (-1 : ℝ)) (fun _ => 1) with hs_def
  have hs : MeasurableSet s := measurableSet_Icc
  -- the derivative within the cube, and its determinant as the matrix's
  have hf' : ∀ x ∈ s, HasFDerivWithinAt f
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (M x))) s x :=
    fun x _ => (hf x).hasFDerivWithinAt
  have hdetf : ∀ x, (LinearMap.toContinuousLinearMap (Matrix.toLin' (M x))).det = (M x).det := by
    intro x
    unfold ContinuousLinearMap.det
    rw [LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']
  -- the integrand is continuous, hence integrable on the cube, and non-negative there
  have hint : Integrable (fun x => (M x).det) (MeasureTheory.volume.restrict s) :=
    (((continuous_id.matrix_det).comp hM).integrableOn_Icc)
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict s] fun x => (M x).det :=
    (ae_restrict_iff' hs).mpr (Filter.Eventually.of_forall fun x hx => hdet x hx)
  -- so the lower integral of `|det|` is the integral of `det`
  have hl : ∫⁻ x in s, ENNReal.ofReal |(LinearMap.toContinuousLinearMap
        (Matrix.toLin' (M x))).det| = ENNReal.ofReal (∫ x in s, (M x).det) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine setLIntegral_congr_fun hs fun x hx => ?_
    rw [hdetf, abs_of_nonneg (hdet x hx)]
  -- Mathlib's two area formulas: the bound, and the equality for an injective map
  refine ⟨?_, fun hinj => ?_⟩
  · rw [← hl]
    exact MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv _ hs hf'
  · rw [← hl]
    exact (MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image _ hs hf' hinj).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
