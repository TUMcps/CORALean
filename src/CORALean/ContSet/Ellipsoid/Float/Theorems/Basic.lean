module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.Materialise
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalQEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalCenterEq
public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalDominated
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

section

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


end


section

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


-- ================================  `Ellipsoid.nominal_of_psd`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- At a positive semi-definite `Q` the nominal part is the ellipsoid of the stored floats. -/
theorem Ellipsoid.nominal_of_psd [SoundFloatArithmetic 𝕋] {E : Ellipsoid 𝕋 n}
    (h : (toRealMat E.Q).PosSemidef) :
    (InflatedContSet.nominal E).ellipsoid = ⟨toRealMat E.Q, toRealVec E.q, h⟩ :=
  Real.Ellipsoid.ofShape_eq h _

end

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
