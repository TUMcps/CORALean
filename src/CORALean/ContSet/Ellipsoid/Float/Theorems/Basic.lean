module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.Mtimes
public import CORALean.ContSet.Ellipsoid.Float.Operations.Plus
public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

@[expose] public section

/-!
# `ContSet/Ellipsoid/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ===============================  `Ellipsoid.convex_construct`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.convex_construct`
carries convexity across: the nominal set is convex as over ℝ, the box because
its coordinates are bounded independently. -/
theorem Ellipsoid.convex_construct (E : Ellipsoid 𝕋 n) : Convex ℝ E.construct :=
  InflatedContSet.convex_construct E

end CORALean.Float


-- =============================  `Ellipsoid.isCompact_construct`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- What this denotes is a nominal set plus an error box, so `InflatedContSet.isCompact_construct`
carries compactness across: the nominal set is compact as over ℝ, the box by
Heine–Borel. -/
theorem Ellipsoid.isCompact_construct (E : Ellipsoid 𝕋 n) : IsCompact E.construct :=
  InflatedContSet.isCompact_construct E

end CORALean.Float


-- ===================================  `Ellipsoid.mtimes_k`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `mtimes` does not change the ball's dimension -/
@[simp] theorem Ellipsoid.mtimes_k (M : Mat 𝕋 m n) (E : Ellipsoid 𝕋 n) :
    (Ellipsoid.mtimes M E).k = E.k := rfl

end CORALean.Float


-- ====================================  `Ellipsoid.plus_k`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

omit [SoundFloatArithmetic 𝕋] in
/-- `plus`'s ball dimension is the sum of the two incoming ones -/
@[simp] theorem Ellipsoid.plus_k (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) :
    (Ellipsoid.plus s₁ s₂ E₁ E₂).k = E₁.k + E₂.k := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
