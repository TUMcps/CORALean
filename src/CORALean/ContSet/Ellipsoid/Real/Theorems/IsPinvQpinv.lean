module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.DmdPinv

@[expose] public section

/-!
# `Q⁺` is the pseudo-inverse of the shape matrix

`Ellipsoid.Qpinv`, the inverse of each eigenvalue of `Q` with `0` staying `0`, meets the four
Penrose conditions, so it is the Moore-Penrose pseudo-inverse the definition names.

Why: the continuous functional calculus turns products of functions of `Q` into products of the
functions, which on reals are `x x⁻¹ x = x` and `x⁻¹ x x⁻¹ = x⁻¹`, `0` included, and every
function of a symmetric `Q` is symmetric. The spectrum of a matrix is finite, so `x⁻¹` is
continuous on it.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* `Q⁺` is the Moore-Penrose pseudo-inverse of `Q`
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `Q⁺` is the Moore-Penrose pseudo-inverse of `Q`. -/
theorem Ellipsoid.isPinv_Qpinv (E : Ellipsoid n) : -- --- CONCL ---
    IsPinv E.Q E.Qpinv := by -- --- PROOF ---
  have ha : IsSelfAdjoint E.Q := E.psd.isHermitian
  have hm : ∀ f g : ℝ → ℝ, cfc f E.Q * cfc g E.Q = cfc (fun x => f x * g x) E.Q := fun f g =>
    (cfc_mul f g E.Q (Matrix.finite_real_spectrum.continuousOn _)
      (Matrix.finite_real_spectrum.continuousOn _)).symm
  have hid : cfc (fun x : ℝ => x) E.Q = E.Q := cfc_id' ℝ E.Q
  have hsa : ∀ f : ℝ → ℝ, (cfc f E.Q)ᵀ = cfc f E.Q := fun f => by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact (cfc_predicate f E.Q : IsSelfAdjoint _)
  have e1 : E.Q * E.Qpinv = cfc (fun x : ℝ => x * x⁻¹) E.Q := by
    calc _ = cfc (fun x : ℝ => x) E.Q * cfc (fun x : ℝ => x⁻¹) E.Q := by rw [hid]; rfl
      _ = _ := hm _ _
  have e2 : E.Qpinv * E.Q = cfc (fun x : ℝ => x * x⁻¹) E.Q := by
    calc _ = cfc (fun x : ℝ => x⁻¹) E.Q * cfc (fun x : ℝ => x) E.Q := by rw [hid]; rfl
      _ = _ := (hm _ _).trans (cfc_congr fun (x : ℝ) _ => mul_comm _ _)
  -- `x x⁻¹ x = x` and `x x⁻¹ x⁻¹ = x⁻¹`, at `0` as well
  have hk : ∀ x : ℝ, x * x⁻¹ * x = x ∧ x * x⁻¹ * x⁻¹ = x⁻¹ := fun x => by
    rcases eq_or_ne x 0 with rfl | hx <;> [simp; exact ⟨by field_simp, by field_simp⟩]
  refine ⟨?_, ?_, by rw [e1, hsa], by rw [e2, hsa]⟩
  · calc _ = cfc (fun x : ℝ => x * x⁻¹) E.Q * cfc (fun x : ℝ => x) E.Q := by rw [e1, hid]
      _ = cfc (fun x : ℝ => x) E.Q := (hm _ _).trans (cfc_congr fun x _ => (hk x).1)
      _ = E.Q := hid
  · rw [e2, Ellipsoid.Qpinv, hm]
    exact cfc_congr fun x _ => (hk x).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
