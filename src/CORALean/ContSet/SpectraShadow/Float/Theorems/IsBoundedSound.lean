import CORALean.ContSet.SpectraShadow.Float.Operations.IsBounded
import CORALean.ContSet.Interval.Float.Theorems.IsCompact

/-!
# A `true` from `SpectraShadow.isBounded` proves the set bounded

The certified interval hull exists and holds the set (`SpectraShadow.interval_contains`), and a
float box is compact, so bounded.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.isBounded_sound {S : SpectraShadow 𝕋 n} {Yup Ylo : Fin n → Mat 𝕋 S.k S.k}
    (h : S.isBounded Yup Ylo = true) : Bornology.IsBounded S.construct := by
  simp only [SpectraShadow.isBounded, Option.isSome_iff_exists] at h
  obtain ⟨I, hI⟩ := h
  exact (Interval.isCompact_construct I).isBounded.subset (SpectraShadow.interval_contains hI)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
