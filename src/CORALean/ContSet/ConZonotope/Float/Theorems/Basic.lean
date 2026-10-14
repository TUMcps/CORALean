module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

@[expose] public section

/-!
# `ContSet/ConZonotope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==============================  `ConZonotope.convex_construct`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently. -/
theorem ConZonotope.convex_construct (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Convex ℝ cZ.construct :=
  InflatedContSet.convex_construct cZ

end CORALean.Float


-- =================================  `ConZonotope.corner_mem`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- When `inf ≤ sup` is certified entry by entry. -/
theorem ConZonotope.corner_mem {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (hE : ∀ i, le (cZ.E.inf i) (cZ.E.sup i) = true) :
    (fun i => toReal (cZ.E.inf i)) ∈ (error cZ).construct := fun i =>
  ⟨le_refl _, toReal_le_of_le (hE i)⟩

end CORALean.Float


-- ============================  `ConZonotope.isCompact_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem ConZonotope.isCompact_construct (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : IsCompact cZ.construct :=
  InflatedContSet.isCompact_construct cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
