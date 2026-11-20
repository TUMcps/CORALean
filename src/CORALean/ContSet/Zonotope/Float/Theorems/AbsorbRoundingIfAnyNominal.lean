module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsorbRoundingIfAny
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsorbRoundingNominal

@[expose] public section

/-!
# `Zonotope.absorbRoundingIfAny` keeps every point in its nominal part

A zero box adds nothing, so the points of the set are those of its nominal part; otherwise the box
has been made into generators (`absorbRounding_nominal`).

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* zonotope is contained in the nominal part of `absorbRoundingIfAny`
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.absorbRoundingIfAny_nominal (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    Z.toSet ⊆ nominalSet Z.absorbRoundingIfAny := by -- --- PROOF ---
  unfold Zonotope.absorbRoundingIfAny
  split_ifs with h
  · rintro _ ⟨z, hz, e, he, rfl⟩
    have h0 : e = 0 := by
      funext i
      have h1 := toReal_le_of_le (decide_eq_true_iff.mp h i).1
      have h2 := toReal_le_of_le (decide_eq_true_iff.mp h i).2
      rw [toReal_zero] at h1 h2
      exact le_antisymm (le_trans (he i).2 h1) (le_trans h2 (he i).1)
    simpa [h0] using hz
  · exact Zonotope.absorbRounding_nominal Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
