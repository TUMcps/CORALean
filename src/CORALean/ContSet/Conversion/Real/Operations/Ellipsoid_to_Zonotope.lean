module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_Interval
public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Theorems.SqNormLeMaxNormSq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# An ellipsoid as a zonotope — the construction

`Ellipsoid.zonotope`, `Ellipsoid.zonotopeInnerNorm` and `Ellipsoid.zonotopeNorm` are the
constructions; `Ellipsoid_to_Zonotope` states and proves what they guarantee.

## References

* [1] V. Gaßmann and M. Althoff. "Scalable Zonotope-Ellipsoid Conversions using the Euclidean
      Zonotope Norm". In Proc. of the 2020 American Control Conference (ACC), pp. 4715-4721,
      2020.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.zonotope (E : Ellipsoid n) : Zonotope (Vec ℝ n) :=
  E.interval.zonotope

/-- [1, Thm. 2]: `Z(r^{-1/2} T⁻¹ S, ē)`, `T⁻¹` the ellipsoid's generator. -/
noncomputable def Ellipsoid.zonotopeInnerNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ E.k)
    (r : ℝ) : Zonotope (Vec ℝ n) where
  h := m
  c := E.c
  G := fun j => (√r)⁻¹ • (E.G *ᵥ S j)

/-- [1, Thm. 4]: `Z(l^{-1/2} T⁻¹ S, ē)`, `T⁻¹` the ellipsoid's generator. -/
noncomputable def Ellipsoid.zonotopeNorm (E : Ellipsoid n) {m : ℕ} (S : Fin m → Vec ℝ E.k)
    (l : ℝ) : Zonotope (Vec ℝ n) where
  h := m
  c := E.c
  G := fun j => (√l)⁻¹ • (E.G *ᵥ S j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
