module

public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.VPolytope.Float.Operations.Materialise
public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.VPolytope.Real.Instances

@[expose] public section

/-!
# `ContSet/VPolytope/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

section

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ===============================  `VPolytope.convex_construct`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently. -/
theorem VPolytope.convex_construct (P : VPolytope (Vec 𝕋 n)) : Convex ℝ P.construct :=
  InflatedContSet.convex_construct P


-- =============================  `VPolytope.isCompact_construct`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem VPolytope.isCompact_construct (P : VPolytope (Vec 𝕋 n)) : IsCompact P.construct :=
  InflatedContSet.isCompact_construct P

end


section

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `VPolytope.materialise_eq`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem VPolytope.materialise_eq (P : VPolytope (Vec 𝕋 n)) : P.materialise = P := by
  simp [VPolytope.materialise]

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
