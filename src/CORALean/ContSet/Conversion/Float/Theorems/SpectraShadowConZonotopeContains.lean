module

public import CORALean.ContSet.Conversion.Float.Theorems.SpectraShadowZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A spectrahedral shadow as a constrained zonotope, over a floating-point scalar

CORA's `conZonotope(zonotope(SpS))`: the certified zonotope enclosure
(`SpectraShadow.zonotope`, the base spectrahedron's dual certificates the caller's) converted by
the float `Zonotope.conZonotope`. `none` when a certificate fails. An enclosure, as over ℝ.

## Inputs
* `S` – spectrahedral shadow
* `Yup` – upper certificate matrices per generator
* `Ylo` – lower certificate matrices per generator

## Hypotheses
* none

## Conclusion
* shadow is contained in every returned constrained zonotope
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.conZonotope_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k} :
    ∀ W ∈ S.conZonotope Yup Ylo,
      S.construct ⊆ W.construct := by
  intro W (h : S.conZonotope Yup Ylo = some W)
  simp only [SpectraShadow.conZonotope, Option.map_eq_some_iff] at h
  obtain ⟨Z, hZ, rfl⟩ := h
  exact subset_trans (SpectraShadow.zonotope_contains _ hZ) (Zonotope.conZonotope_contains Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
