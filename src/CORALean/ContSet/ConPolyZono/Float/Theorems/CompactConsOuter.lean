module

public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactCons
public import CORALean.ContSet.ConPolyZono.Float.Theorems.MemNominalSet
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.MemCompactOfMem

@[expose] public section

/-!
# `compactCons` over-approximates, merging constraint rows

A merged constraint row has no ambient box to reach, so the slack absorbs it: the factors are in
`[-1,1]`, where the constraint's own `PolyLevelSet.compact` admits every factor vector it did
(`PolyLevelSet.mem_compact_of_mem`). The nominal set only *grows*, and the error box does not
move.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Hypotheses
* none

## Conclusion
* the set is contained in the result
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Only the constraint weakens, so the nominal set grows and the error box does
not move. -/
private theorem ConPolyZono.aux_compactCons_nominal (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    nominalSet cPZ ⊆ nominalSet cPZ.compactCons := by
  intro x hx
  obtain ⟨a, β, ha, hβ, hsat, hxi⟩ := ConPolyZono.mem_nominalSet_iff.mp hx
  exact ConPolyZono.mem_nominalSet_iff.mpr
    ⟨a, β, ha, hβ, PolyLevelSet.mem_compact_of_mem cPZ.cons cPZ.cons_eq ha hsat, hxi⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.compactCons_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.compactCons.construct :=
  InflatedContSet.mono_subset (ConPolyZono.aux_compactCons_nominal cPZ) (subset_refl _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
