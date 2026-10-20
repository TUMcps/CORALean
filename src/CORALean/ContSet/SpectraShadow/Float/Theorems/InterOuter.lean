module

public import CORALean.ContSet.SpectraShadow.Float.Operations.Inter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.SpectraShadow.Float.Theorems.TieInterOuter

@[expose] public section

/-!
# `SpectraShadow.inter` contains the intersection

Each shadow lies in its absorbed nominal shadow (`absorbRounding_nominal`), and the tied shadow
contains the intersection of the two nominal shadows (`tieInter_outer`).

## Inputs
* `S₁` – spectrahedral shadow
* `S₂` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.inter` contains the intersection
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.inter_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
    S₁.construct ∩ S₂.construct ⊆ (S₁.inter S₂).construct :=
  subset_trans (Set.inter_subset_inter S₁.absorbRounding_nominal S₂.absorbRounding_nominal)
    (SpectraShadow.tieInter_outer _ _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
