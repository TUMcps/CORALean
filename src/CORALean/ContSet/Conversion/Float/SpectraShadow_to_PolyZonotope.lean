import CORALean.ContSet.Conversion.Float.SpectraShadow_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_PolyZonotope

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

def SpectraShadow.polyZonotope (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (PolyZonotope (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.polyZonotope


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.polyZonotope_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k} {W : PolyZonotope (Vec 𝕋 n)}
    (h : S.polyZonotope Yup Ylo = some W) :
    S.construct ⊆ W.construct := by
  simp only [SpectraShadow.polyZonotope, Option.map_eq_some_iff] at h
  obtain ⟨Z, hZ, rfl⟩ := h
  exact subset_trans (SpectraShadow.zonotope_contains hZ) (Zonotope.polyZonotope_contains Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
