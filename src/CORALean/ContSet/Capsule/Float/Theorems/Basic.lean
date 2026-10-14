module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Float.Operations.Reduce
public import CORALean.ContSet.Capsule.Float.Operations.Reindex
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.CentreMemConstructIff
public import CORALean.ContSet.Capsule.Real.Theorems.ReindexExact

@[expose] public section

/-!
# `ContSet/Capsule/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ============================  `Capsule.centre_mem_construct_iff`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- It is in the capsule exactly when the stored radius is non-negative. -/
theorem Capsule.centre_mem_construct_iff (C : Capsule 𝕋 n) :
    toRealVec C.c ∈ C.construct ↔ 0 ≤ toReal C.r :=
  CORALean.Real.Capsule.centre_mem_construct_iff C.nominal

end CORALean.Float


-- ================================  `Capsule.convex_construct`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What it denotes is the exact capsule's set, so the exact theorem applies. -/
theorem Capsule.convex_construct (C : Capsule 𝕋 n) : Convex ℝ C.construct :=
  CORALean.Real.Capsule.convex_construct C.nominal

end CORALean.Float


-- ==============================  `Capsule.isCompact_construct`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What it denotes is the exact capsule's set, so the exact theorem applies. -/
theorem Capsule.isCompact_construct (C : Capsule 𝕋 n) : IsCompact C.construct :=
  CORALean.Real.Capsule.isCompact_construct C.nominal

end CORALean.Float


-- ==================================  `Capsule.reduce_outer`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-- `reduce` is the identity, so it encloses trivially. -/
theorem Capsule.reduce_outer (C : Capsule 𝕋 n) (o : ℕ) :
    C.construct ⊆ (C.reduce o).construct :=
  subset_rfl

end CORALean.Float


-- =================================  `Capsule.reindex_exact`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-- The exact layer's `reindex` of the nominal capsule is the nominal capsule of the result, so
`Real.Capsule.reindex_exact` is the equality, as over ℝ: nothing is rounded. -/
theorem Capsule.reindex_exact (e : Fin m ≃ Fin n) (C : Capsule 𝕋 n) :
    (C.reindex e).construct = reindexLin e '' C.construct :=
  Real.Capsule.reindex_exact e C.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
