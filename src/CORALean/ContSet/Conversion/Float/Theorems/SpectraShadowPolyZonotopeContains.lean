module

public import CORALean.ContSet.Conversion.Float.Theorems.SpectraShadowZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopePolyZonotopeContains
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains

@[expose] public section

/-!
# A spectrahedral shadow as a polynomial zonotope, over a floating-point scalar

CORA's `polyZonotope(zonotope(SpS))`: the certified zonotope enclosure
(`SpectraShadow.zonotope`, the base spectrahedron's dual certificates the caller's) converted by
the float `Zonotope.polyZonotope`. `none` when a certificate fails. An enclosure, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.polyZonotope_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k} :
    ∀ W ∈ S.polyZonotope Yup Ylo,
      S.construct ⊆ W.construct := by
  intro W (h : S.polyZonotope Yup Ylo = some W)
  simp only [SpectraShadow.polyZonotope, Option.map_eq_some_iff] at h
  obtain ⟨Z, hZ, rfl⟩ := h
  exact subset_trans (SpectraShadow.zonotope_contains _ hZ) (Zonotope.polyZonotope_contains Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
