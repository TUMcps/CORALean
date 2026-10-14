module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.Materialise
public import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `ContSet/Ellipsoid/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ===============================  `Ellipsoid.convex_construct`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently. -/
theorem Ellipsoid.convex_construct (E : Ellipsoid 𝕋 n) : Convex ℝ E.construct :=
  InflatedContSet.convex_construct E


-- =============================  `Ellipsoid.isCompact_construct`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem Ellipsoid.isCompact_construct (E : Ellipsoid 𝕋 n) : IsCompact E.construct :=
  InflatedContSet.isCompact_construct E


-- ===================================  `Ellipsoid.mtimes_k`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `mtimes` does not change the ball's dimension -/
@[simp] theorem Ellipsoid.mtimes_k (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (Ellipsoid.mtimes M E).k = E.k := rfl


-- ====================================  `Ellipsoid.plus_k`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

omit [SoundFloatArithmetic 𝕋] in
/-- `plus`'s ball dimension is the sum of the two incoming ones -/
@[simp] theorem Ellipsoid.plus_k (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).k = E₁.k + E₂.k := rfl

end CORALean.Float


namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ================================  `Ellipsoid.materialise_eq`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

omit [FloatOps 𝕋] in
/-- `materialise` is the identity: it changes only what running the definition costs. -/
@[simp] theorem Ellipsoid.materialise_eq (E : Ellipsoid 𝕋 n) : E.materialise = E := by
  simp [Ellipsoid.materialise]


-- ==================================  `Ellipsoid.nominal_G`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal Ellipsoid's field `G`, so proofs can see through the instance. -/
theorem Ellipsoid.nominal_G [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).G = toRealMat E.G := rfl


-- ==================================  `Ellipsoid.nominal_k`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal ellipsoid's fields, so proofs can see through the instance. -/
theorem Ellipsoid.nominal_k [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).k = E.k := rfl


-- ==================================  `Ellipsoid.nominal_q`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- The nominal Ellipsoid's field `c`, so proofs can see through the instance. -/
theorem Ellipsoid.nominal_q [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).c = toRealVec E.c := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
