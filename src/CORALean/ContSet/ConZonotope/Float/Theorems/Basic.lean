module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.ConZonotope.Float.Operations.InteriorCert
public import CORALean.ContSet.ConZonotope.Float.Operations.Materialise
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `ContSet/ConZonotope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ==============================  `ConZonotope.convex_construct`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently. -/
theorem ConZonotope.convex_construct (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : Convex ℝ cZ.construct :=
  InflatedContSet.convex_construct cZ


-- =================================  `ConZonotope.corner_mem`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- When `inf ≤ sup` is certified entry by entry. -/
theorem ConZonotope.corner_mem {cZ : ConZonotope 𝕋 (Vec 𝕋 n)}
    (hE : ∀ i, le (cZ.I_error.inf i) (cZ.I_error.sup i) = true) :
    (fun i => toReal (cZ.I_error.inf i)) ∈ (I_error cZ).construct := fun i =>
  ⟨le_refl _, toReal_le_of_le (hE i)⟩


-- ============================  `ConZonotope.isCompact_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem ConZonotope.isCompact_construct (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : IsCompact cZ.construct :=
  InflatedContSet.isCompact_construct cZ

end CORALean.Float


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ===============================  `ConZonotope.materialise_eq`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem ConZonotope.materialise_eq (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    cZ.materialise = cZ := by
  simp [ConZonotope.materialise]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
