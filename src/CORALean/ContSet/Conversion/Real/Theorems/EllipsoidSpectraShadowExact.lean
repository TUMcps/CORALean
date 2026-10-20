module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidPosSemidefSpectraShadowIff

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow

`Ellipsoid.spectraShadow_exact`: its `spectraShadow` is exactly it. The free variables are the
point itself (`c = 0`, `G = I`), and the Schur form at a point is positive semi-definite iff the
point is in the ellipsoid (`posSemidef_spectraShadow_iff`).

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* ellipsoid equals its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.spectraShadow_exact (E : Ellipsoid n) : -- --- CONCL ---
    E.construct = E.spectraShadow.construct := by -- --- PROOF ---
  -- the shadow's point is its free variable
  have hx : ∀ u : Vec ℝ n, E.spectraShadow.c + ∑ i, u i • E.spectraShadow.G i = u := fun u => by
    funext r
    simp [Ellipsoid.spectraShadow, Finset.sum_apply, Pi.single_apply]
  ext x
  constructor
  · intro hxE
    exact ⟨x, (Ellipsoid.posSemidef_spectraShadow_iff E x).mpr hxE, (hx x).symm⟩
  · rintro ⟨u, hu, rfl⟩
    have h := (Ellipsoid.posSemidef_spectraShadow_iff E u).mp hu
    rwa [← hx u] at h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
