module

public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Operations.RepresentsaPoint
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.EuclideanNorm
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-!
# `ContSet/Zonotope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =====================================  `Zonotope.embed`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {n N : ℕ}

/-- The zero-padding map: coordinate `proj k` of the image is coordinate `k`, all others are `0`.
It is the transpose of the selection matrix, and linear. -/
def Zonotope.embed (proj : Fin n → Fin N) : Vec ℝ n →ₗ[ℝ] Vec ℝ N :=
  Matrix.mulVecLin (Matrix.of fun (i : Fin N) (k : Fin n) => if proj k = i then (1 : ℝ) else 0)

end CORALean.Real


-- ================================  `Zonotope.generatorLength`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open CORALean

variable {n : ℕ}

/-- The Euclidean length `‖Gⱼ‖₂` of generator `j`.

CORA's `@zonotope/generatorLength.m`: `vecnorm(Z.G)`, the Euclidean length of each generator. -/
noncomputable def Zonotope.generatorLength (Z : Zonotope (Vec ℝ n)) (j : Fin Z.h) : ℝ :=
  ‖Z.G j‖₂

end CORALean.Real


-- =================================  `Zonotope.mtimes_eq_map`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

variable {n m : ℕ}

/-- True by `rfl`, and what lets `mtimes` inherit `map`'s exactness. -/
theorem Zonotope.mtimes_eq_map (M : Mat ℝ m n) (Z : Zonotope (Vec ℝ n)) :
    Zonotope.mtimes M Z = Z.map (Matrix.mulVecLin M) := rfl

end CORALean.Real


-- ====================================  `Zonotope.project`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n m : ℕ}

/-- CORA's `@zonotope/project`: the centre and every generator at the chosen coordinates. `dims` may
repeat or reorder coordinates. Reading coordinates is linear, so this is `map` at the selection
map, and `project_exact` is `map_exact`. -/
def Zonotope.project (Z : Zonotope (Vec ℝ n)) (dims : Fin m → Fin n) : Zonotope (Vec ℝ m) :=
  Z.map (LinearMap.funLeft ℝ ℝ dims)

end CORALean.Real


-- ==============================  `Zonotope.representsa_origin`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- `zonotope/representsa_` at `origin`.

CORA's `@zonotope/representsa_` at type `origin` with tolerance `0`: a point at `0`. -/
def Zonotope.representsa_origin (Z : Zonotope α) : Prop := Z.c = 0 ∧ Z.representsa_point

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
