module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.Operations.CompactFactors
public import CORALean.ContSet.ConPolyZono.Float.Operations.Mtimes
public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Theorems.CompactFactorsNominal
public import CORALean.ContSet.ConPolyZono.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

@[expose] public section

/-!
# `ContSet/ConPolyZono/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

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


-- ==============================  `ConPolyZono.toRealVec_append`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Appending two float vectors and reading back commutes -/
theorem ConPolyZono.toRealVec_append {m₁ m₂ : ℕ} (b₁ : Vec 𝕋 m₁) (b₂ : Vec 𝕋 m₂) :
    toRealVec (Fin.append b₁ b₂) = Fin.append (toRealVec b₁) (toRealVec b₂) := by
  refine funext (Fin.addCases (fun i => ?_) (fun i => ?_)) <;>
    simp only [toRealVec, Fin.append_left, Fin.append_right]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
