module

public import CORALean.ContSet.Conversion.Float.SpectraShadow_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_ZonoBundle
public import CORALean.ContSet.Conversion.Float.Operations.SpectraShadow_to_ZonoBundle

@[expose] public section

/-!
# A spectrahedral shadow as a zonotope bundle, over a floating-point scalar

CORA's `zonoBundle(zonotope(SpS))`: the certified zonotope enclosure
(`SpectraShadow.zonotope`, the base spectrahedron's dual certificates the caller's) converted by
the float `Zonotope.zonoBundle`. `none` when a certificate fails. An enclosure, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.zonoBundle_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k} {W : ZonoBundle (Vec 𝕋 n)}
    (h : S.zonoBundle Yup Ylo = some W) :
    S.construct ⊆ W.construct := by
  simp only [SpectraShadow.zonoBundle, Option.map_eq_some_iff] at h
  obtain ⟨Z, hZ, rfl⟩ := h
  exact subset_trans (SpectraShadow.zonotope_contains hZ) (Zonotope.zonoBundle_exact Z).subset

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
