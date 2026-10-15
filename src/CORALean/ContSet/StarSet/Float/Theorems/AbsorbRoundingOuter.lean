module

public import CORALean.ContSet.InflatedContSet.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.StarSet.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `StarSet.absorbRounding` loses no point

Read back through `ContSet`: the set lies in the nominal set of `absorbRounding`, and that box is
the origin, so it lies in the whole.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float.SoundFloatArithmetic Float.FloatOps InflatedContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `absorbRounding` contains the set. -/
theorem StarSet.absorbRounding_outer (s : StarSet 𝕋 n) :
    s.construct ⊆ s.absorbRounding.construct :=
  (s.absorbRounding_nominal).trans (nominalSet_subset_construct
    (by
      show (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
      rw [Interval.origin_exact]
      exact Set.mem_singleton _))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
