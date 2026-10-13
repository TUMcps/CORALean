import CORALean.ContSet.Conversion.Float.SpectraShadow_to_Zonotope
import CORALean.ContSet.Conversion.Float.Zonotope_to_ConPolyZono

/-!
# A spectrahedral shadow as a constrained polynomial zonotope, over a floating-point scalar

CORA's `conPolyZono(zonotope(SpS))`: the certified zonotope enclosure
(`SpectraShadow.zonotope`, the base spectrahedron's dual certificates the caller's) converted by
the float `Zonotope.conPolyZono`. `none` when a certificate fails. An enclosure, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}

def SpectraShadow.conPolyZono (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k) :
    Option (ConPolyZono 𝕋 (Vec 𝕋 n)) :=
  (S.zonotope Yup Ylo).map Zonotope.conPolyZono


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.conPolyZono_contains {S : SpectraShadow 𝕋 (Vec 𝕋 n)}
    {Yup Ylo : Fin S.m → Mat 𝕋 S.k S.k} {W : ConPolyZono 𝕋 (Vec 𝕋 n)}
    (h : S.conPolyZono Yup Ylo = some W) :
    S.construct ⊆ W.construct := by
  simp only [SpectraShadow.conPolyZono, Option.map_eq_some_iff] at h
  obtain ⟨Z, hZ, rfl⟩ := h
  exact subset_trans (SpectraShadow.zonotope_contains hZ) (Zonotope.conPolyZono_contains Z)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
