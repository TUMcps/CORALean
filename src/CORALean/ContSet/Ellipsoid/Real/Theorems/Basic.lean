module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose2
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.Project
public import CORALean.ContSet.Ellipsoid.Real.Operations.Shape
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.SegmentsSubsetOfIsOrOuter

@[expose] public section

/-!
# `ContSet/Ellipsoid/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ================================  `Ellipsoid.dot_transpose`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `(Gᵀ w) · a = w · (G a)`, the identity behind the support point and the shape matrix `G Gᵀ`. -/
theorem Ellipsoid.dot_transpose {k : ℕ} (G : Mat ℝ n k) (w : Vec ℝ n) (a : Vec ℝ k) :
    (Gᵀ *ᵥ w) ⬝ᵥ a = w ⬝ᵥ (G *ᵥ a) := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]


-- ================================  `Ellipsoid.enclose₂_outer`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Outer, given the hull `orOA` encloses both operands (`Ellipsoid.IsOrOuter`). -/
theorem Ellipsoid.enclose₂_outer (orOA : Ellipsoid n → Ellipsoid n → Ellipsoid n)
    (hor : ∀ E₁ E₂, Ellipsoid.IsOrOuter E₁ E₂ (orOA E₁ E₂)) (E E2 : Ellipsoid n) :
    segments E.construct E2.construct ⊆ (Ellipsoid.enclose₂ orOA E E2).construct :=
  Ellipsoid.segments_subset_of_isOrOuter (hor _ _)


-- =============================  `Ellipsoid.isBounded_construct`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Read off compactness rather than proved again: `‖G u‖ ≤ ‖G‖ ‖u‖₂` would need the
operator norm, and the compactness proof already carries everything. -/
theorem Ellipsoid.isBounded_construct (E : Ellipsoid n) : Bornology.IsBounded E.construct :=
  E.isCompact_construct.isBounded


-- ==============================  `Ellipsoid.isClosed_construct`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---

/-- Read off compactness, as for a zonotope and for the same reason: `construct` is
an affine image, and an affine image of a merely closed set need not be closed. -/
theorem Ellipsoid.isClosed_construct (E : Ellipsoid n) : IsClosed E.construct :=
  E.isCompact_construct.isClosed


-- ================================  `Ellipsoid.mem_construct`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An introduction rather than a characterisation: any affine image of a unit
ball point is a point the ellipsoid contains. `Theorems/QMemConstruct` is the
same statement at `u = 0`, the centre. -/
theorem Ellipsoid.mem_construct {E : Ellipsoid n} {u : Vec ℝ E.k} (hu : ‖u‖₂ ≤ 1) :
    E.c + E.G *ᵥ u ∈ E.construct := ⟨u, hu, rfl⟩


-- =============================  `Ellipsoid.centre_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `center` is the field `q`; it is the image of the zero coefficient vector,
whatever the generators. -/
theorem Ellipsoid.centre_mem_construct (E : Ellipsoid n) : E.c ∈ E.construct := by
  have hu : ‖(0 : Vec ℝ E.k)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
  simpa using Ellipsoid.mem_construct (E := E) hu


-- =================================  `Ellipsoid.mem_ofPoint`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ofPoint v` reuses `mem_construct` at `u = 0 : Vec ℝ 0`, the only coefficient
vector a `0`-column `G` admits, in `unitBall₂` because `norm₂_zero ≤ 1`. -/
theorem Ellipsoid.mem_ofPoint (v : Vec ℝ n) : v ∈ (Ellipsoid.ofPoint v).construct := by
  have hu : ‖(0 : Vec ℝ 0)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
  simpa [Ellipsoid.ofPoint] using Ellipsoid.mem_construct (E := Ellipsoid.ofPoint v) hu


-- ================================  `Ellipsoid.project_exact`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost. -/
theorem Ellipsoid.project_exact (E : Ellipsoid n) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' E.construct = (E.project dims).construct :=
  Ellipsoid.map_exact (LinearMap.funLeft ℝ ℝ dims) E


-- ===================================  `Ellipsoid.quad_eq`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `vᵀ Q v = (Gᵀ v)ᵀ (Gᵀ v)` for `Q = G Gᵀ`, so it is `‖Gᵀ v‖₂²` and nonnegative. -/
theorem Ellipsoid.quad_eq (E : Ellipsoid n) (v : Vec ℝ n) :
    v ⬝ᵥ (E.shape *ᵥ v) = (E.Gᵀ *ᵥ v) ⬝ᵥ (E.Gᵀ *ᵥ v) := by
  rw [Ellipsoid.shape, ← Matrix.mulVec_mulVec, Ellipsoid.dot_transpose]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
