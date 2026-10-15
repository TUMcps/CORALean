module

public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm
public import CORALean.Global.MatVec
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `ContSet/Zonotope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix CORALean

variable {n m N : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  `Zonotope.embed`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- The zero-padding map: coordinate `proj k` of the image is coordinate `k`, all others are `0`.
It is the transpose of the selection matrix, and linear. -/
def Zonotope.embed (proj : Fin n → Fin N) : Vec ℝ n →ₗ[ℝ] Vec ℝ N :=
  Matrix.mulVecLin (Matrix.of fun (i : Fin N) (k : Fin n) => if proj k = i then (1 : ℝ) else 0)


-- ================================  `Zonotope.generatorLength`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The Euclidean length `‖Gⱼ‖₂` of generator `j`.

CORA's `@zonotope/generatorLength.m`: `vecnorm(Z.G)`, the Euclidean length of each generator. -/
noncomputable def Zonotope.generatorLength (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  ‖Z.G j‖₂


-- =================================  `Zonotope.mtimes_eq_map`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem Zonotope.mtimes_eq_map (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope.mtimes M Z = Z.map (Matrix.mulVecLin M) := rfl


-- ====================================  `Zonotope.project`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@zonotope/project`: the center and every generator at the chosen coordinates. `dims` may
repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the selection
map, and `project_exact` is `map_exact`. -/
def Zonotope.project (Z : Zonotope (Vec ℝ n)) (dims : Fin m → Fin n) : Zonotope (Vec ℝ m) :=
  Z.map (LinearMap.funLeft ℝ ℝ dims)


-- ==============================  `Zonotope.representsa_origin`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `zonotope/representsa_` at `origin`.

CORA's `@zonotope/representsa_` at type `origin` with tolerance `0`: a point at `0`. -/
def Zonotope.representsa_origin (Z : Zonotope α) : Prop := Z.c = 0 ∧ Z.representsa_point


-- ===================================  `Zonotope.transpose`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `@matZonotope/transpose`: the center and every generator transposed. -/
def Zonotope.transpose (Z : Zonotope (Mat ℝ m n)) : Zonotope (Mat ℝ n m) :=
  Z.map (Matrix.transposeLinearEquiv (Fin m) (Fin n) ℝ ℝ).toLinearMap


-- ======================================  `Zonotope.vec`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `zonotope(matZ)`: the center and the generators stacked column by column
(`reshape(·, [], 1)`), a zonotope in the space of `n * m` entries. -/
def Zonotope.vec (Z : Zonotope (Mat ℝ m n)) : Zonotope (Vec ℝ (n * m)) :=
  Z.map matVecEquiv.toLinearMap


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
