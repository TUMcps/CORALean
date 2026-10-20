module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
public import CORALean.ContSet.ConPolyZono.Float.Theorems.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactConsOuter
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactGensOuter

@[expose] public section

/-!
# `compact` over-approximates, where the exact one is an equality

`compactGens` merges generator columns and rounds, `compactCons` merges
constraint rows and widens `b`, and `compactFactors` then drops unused factors
for free.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compact_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.compact.construct := by
  simp only [ConPolyZono.compact, ConPolyZono.materialise_eq]
  exact subset_trans (ConPolyZono.compactGens_outer cPZ)
    (subset_trans (ConPolyZono.compactCons_outer cPZ.compactGens)
      (ConPolyZono.compactFactors_outer cPZ.compactGens.compactCons))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
