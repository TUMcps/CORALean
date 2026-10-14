module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidPosSemidefSpectraShadowIff

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow

`Ellipsoid.spectraShadow_exact`: its `spectraShadow` is exactly it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.spectraShadow_exact (E : Ellipsoid n) :
    E.construct = E.spectraShadow.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, (Ellipsoid.posSemidef_spectraShadow_iff E u).mpr hu, ?_⟩
    funext r
    simp only [Ellipsoid.spectraShadow, Matrix.mulVec, dotProduct, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, (Ellipsoid.posSemidef_spectraShadow_iff E u).mp hu, ?_⟩
    funext r
    simp only [Ellipsoid.spectraShadow, Matrix.mulVec, dotProduct, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
