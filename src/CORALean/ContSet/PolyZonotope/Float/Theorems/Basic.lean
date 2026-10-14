module

public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Float.Operations.LinComb
public import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes
public import CORALean.ContSet.PolyZonotope.Float.Operations.Plus
public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Float.Operations.RepTab
public import CORALean.ContSet.PolyZonotope.Float.Operations.Restructure
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.ContSet.PolyZonotope.Float.Theorems.CompactFactorsNominal
public import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentOuter
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter
public import CORALean.ContSet.PolyZonotope.Real.Instances
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMapE

@[expose] public section

/-!
# `ContSet/PolyZonotope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===========================  `PolyZonotope.compactFactors_outer`  ============================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Costs nothing at all: `compactFactors_nominal` already is the exact equality. -/
theorem PolyZonotope.compactFactors_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.compactFactors.construct :=
  InflatedContSet.mono_subset (PolyZonotope.compactFactors_nominal pZ).subset
    (subset_refl _)

end CORALean.Float


-- ================================  `PolyZonotope.dependent_q`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- Every one of them was made dependent. -/
@[simp] theorem PolyZonotope.dependent_q (pZ : PolyZonotope (Vec 𝕋 n)) : pZ.dependent.q = 0 := rfl

end CORALean.Float


-- ============================  `PolyZonotope.isCompact_construct`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem PolyZonotope.isCompact_construct (pZ : PolyZonotope (Vec 𝕋 n)) : IsCompact pZ.construct :=
  InflatedContSet.isCompact_construct pZ

end CORALean.Float


-- =================================  `PolyZonotope.linComb_h`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- The two incoming blocks, plus the fresh segment block the same size again. -/
@[simp] theorem PolyZonotope.linComb_h (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (pZ₁.linComb pZ₂).h = pZ₁.h + pZ₂.h + (pZ₁.h + pZ₂.h + 1) := rfl

end CORALean.Float


-- =================================  `PolyZonotope.linComb_q`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- No fresh independent factor: the segment's own coefficient is dependent. -/
@[simp] theorem PolyZonotope.linComb_q (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (pZ₁.linComb pZ₂).q = pZ₁.q + pZ₂.q := rfl

end CORALean.Float


-- =================================  `PolyZonotope.mtimes_h`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `mtimes` does not change the dependent generator count -/
@[simp] theorem PolyZonotope.mtimes_h (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (PolyZonotope.mtimes M pZ).h = pZ.h := rfl

end CORALean.Float


-- =================================  `PolyZonotope.mtimes_q`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `mtimes` does not change the independent generator count -/
@[simp] theorem PolyZonotope.mtimes_q (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    (PolyZonotope.mtimes M pZ).q = pZ.q := rfl

end CORALean.Float


-- ==================================  `PolyZonotope.plus_h`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `plus`'s dependent generator count is the sum of the two incoming ones -/
@[simp] theorem PolyZonotope.plus_h (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (pZ₁.plus pZ₂).h = pZ₁.h + pZ₂.h := rfl

end CORALean.Float


-- ==================================  `PolyZonotope.plus_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `plus`'s independent generator count is the sum of the two incoming ones -/
@[simp] theorem PolyZonotope.plus_q (pZ₁ pZ₂ : PolyZonotope (Vec 𝕋 n)) :
    (pZ₁.plus pZ₂).q = pZ₁.q + pZ₂.q := rfl

end CORALean.Float


-- =============================  `PolyZonotope.quadMapE_nominal`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The exponent bookkeeping is the same term in both layers.

`quadMapE` is `rfl`-equal across the layers, being a sum of naturals either way. -/
theorem PolyZonotope.quadMapE_nominal (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope.quadMapE pZ = Real.PolyZonotope.quadMapE (nominal pZ) := rfl

end CORALean.Float


-- ================================  `PolyZonotope.repTab_getD`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {p h : ℕ}

/-- The table agrees with the function it tabulates, which is all a reader of it needs. -/
theorem PolyZonotope.repTab_getD (E : Fin p → Fin h → ℕ) (l : Fin h) :
    (PolyZonotope.repTab E).getD l.val l = Real.PolyZonotope.rep E l := by
  simp [PolyZonotope.repTab, Array.getD_eq_getD_getElem?]

end CORALean.Float


-- =============================  `PolyZonotope.restructure_outer`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- Boxing the independent block is the step that widens; making the box dependent only adds
a zero to the error box. -/
theorem PolyZonotope.restructure_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.restructure.construct :=
  (PolyZonotope.reduceBy_outer pZ _ _).trans (PolyZonotope.dependent_outer _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
