module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Float.Operations.Materialise
public import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsNominal
public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `ContSet/ConPolyZono/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

section

open FloatOps SoundFloatArithmetic InflatedContSet Pointwise Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k : ℕ}


-- ============================  `ConPolyZono.compactFactors_outer`  ============================ --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Costs nothing at all: `compactFactors_nominal` already is the exact equality. -/
theorem ConPolyZono.compactFactors_outer (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.construct ⊆ cPZ.compactFactors.construct :=
  InflatedContSet.mono_subset (ConPolyZono.compactFactors_nominal cPZ).subset (subset_refl _)


-- ============================  `ConPolyZono.isCompact_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem ConPolyZono.isCompact_construct (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) : IsCompact cPZ.construct :=
  InflatedContSet.isCompact_construct cPZ


-- ==================================  `ConPolyZono.mtimes_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- The image is read off the same factor vectors, so nothing about the dependent
block's shape moves. -/
@[simp] theorem ConPolyZono.mtimes_h (M : Mat 𝕋 k n) (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (ConPolyZono.mtimes M cPZ).h = cPZ.h := rfl


-- ===================================  `ConPolyZono.plus_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- The two blocks concatenate, so `h` adds. -/
@[simp] theorem ConPolyZono.plus_h (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    (cPZ₁.plus cPZ₂).h = cPZ₁.h + cPZ₂.h := rfl


end


section

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===============================  `ConPolyZono.materialise_eq`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem ConPolyZono.materialise_eq (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    cPZ.materialise = cPZ := by
  simp [ConPolyZono.materialise]

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
