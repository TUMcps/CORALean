module

public import CORALean.ContSet.InflatedContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `SpectraShadow.absorbRounding` loses no point

Read back through `ContSet`: the set lies in the nominal set of `absorbRounding`, and that box is
the origin, so it lies in the whole.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `absorbRounding` contains the set. -/
theorem SpectraShadow.absorbRounding_outer (S : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    S.construct ⊆ S.absorbRounding.construct :=
  (S.absorbRounding_nominal).trans (nominalSet_subset_construct
    (by
      show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
      rw [Interval.origin_exact]
      exact Set.mem_singleton _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
