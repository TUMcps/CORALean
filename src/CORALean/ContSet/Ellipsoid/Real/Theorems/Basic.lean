module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructEqSqrt
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Theorems.GMulTranspose
public import CORALean.ContSet.Ellipsoid.Real.Operations.Enclose2
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfPoint
public import CORALean.ContSet.Ellipsoid.Real.Operations.Project
public import CORALean.ContSet.Ellipsoid.Real.Operations.Rank
public import CORALean.ContSet.Ellipsoid.Real.Theorems.IsCompact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MapExact
public import CORALean.ContSet.Ellipsoid.Real.Theorems.SetLinCombSubsetOfIsOrOuter
public import CORALean.ContSet.Ellipsoid.Real.Operations.DualVec

@[expose] public section

/-!
# `ContSet/Ellipsoid/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n m : ℕ}


-- ==================================  `apply_eq_dotProduct`  =================================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- A functional applied is the dot product with its `dualVec` -/
theorem apply_eq_dotProduct (c : Vec ℝ n →ₗ[ℝ] ℝ) (x : Vec ℝ n) : c x = dualVec c ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ c x, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; exact mul_comm _ _


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
    Set.linComb E.construct E2.construct ⊆ (Ellipsoid.enclose₂ orOA E E2).construct :=
  Ellipsoid.setLinComb_subset_of_isOrOuter (hor _ _)


-- =====================================  `Ellipsoid.ext`  ====================================== --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Two ellipsoids with the same shape matrix and center are equal, the remaining field a proof. -/
theorem Ellipsoid.ext {E F : Ellipsoid n} (hQ : E.Q = F.Q) (hq : E.q = F.q) : E = F := by
  cases E; cases F; subst hQ hq; rfl


-- ================================  `Ellipsoid.G_eq_zero_iff`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The generator `Q^(1/2)` vanishes iff the shape matrix does (`CFC.sqrt_eq_zero_iff`): a point,
and only a point, has the zero square root. -/
theorem Ellipsoid.G_eq_zero_iff (E : Ellipsoid n) : E.G = 0 ↔ E.Q = 0 :=
  CFC.sqrt_eq_zero_iff E.Q E.psd.nonneg


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
same statement at `u = 0`, the center. -/
theorem Ellipsoid.mem_construct {E : Ellipsoid n} {u : Vec ℝ n} (hu : ‖u‖₂ ≤ 1) :
    E.q + E.G *ᵥ u ∈ E.construct := E.construct_eq_sqrt ▸ ⟨u, hu, rfl⟩


-- =============================  `Ellipsoid.center_mem_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `center` is the field `q`; it is the image of the zero coefficient vector,
whatever the generators. -/
theorem Ellipsoid.center_mem_construct (E : Ellipsoid n) : E.q ∈ E.construct := by
  have hu : ‖(0 : Vec ℝ n)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
  simpa using Ellipsoid.mem_construct (E := E) hu


-- =================================  `Ellipsoid.mem_ofPoint`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ofPoint v` reuses `mem_construct` at `u = 0`, in `unitBall₂` because `norm₂_zero ≤ 1`. -/
theorem Ellipsoid.mem_ofPoint (v : Vec ℝ n) : v ∈ (Ellipsoid.ofPoint v).construct := by
  have hu : ‖(0 : Vec ℝ n)‖₂ ≤ 1 := mem_unitBall₂.mp zero_mem_unitBall₂
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
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- `vᵀ Q v = (Gᵀ v)ᵀ (Gᵀ v)` for `Q = G Gᵀ`, so it is `‖Gᵀ v‖₂²` and nonnegative. -/
theorem Ellipsoid.quad_eq (E : Ellipsoid n) (v : Vec ℝ n) :
    v ⬝ᵥ (E.Q *ᵥ v) = (E.Gᵀ *ᵥ v) ⬝ᵥ (E.Gᵀ *ᵥ v) := by
  rw [← E.G_mul_transpose, ← Matrix.mulVec_mulVec, Ellipsoid.dot_transpose]


-- ================================  `Ellipsoid.rank_eq_rank_G`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `rank(E)`, the rank of `Q`, is that of `G = Q^(1/2)`: the dimension of the subspace the
ellipsoid spans about its center. -/
theorem Ellipsoid.rank_eq_rank_G (E : Ellipsoid n) : E.rank = E.G.rank := by
  rw [Ellipsoid.rank, ← E.G_mul_transpose, Matrix.rank_self_mul_transpose]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
