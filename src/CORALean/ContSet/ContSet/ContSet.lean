module

public import CORALean.ContSet.ContSet.Interfaces

@[expose] public section

/-!
# The sets that need no representation of their own

What denotes a set without being one of the representations under `ContSet/`: a plain `Set`,
which denotes itself, and a matrix, which denotes the singleton it is, as a set of matrices
and, through `LinMapSet`, as the one linear map it applies on vectors or on matrices from the
left. The classes these instantiate are in `Interfaces.lean`.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       16-August-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar ContSet


-- ======================================  MAIN INSTANCE  ======================================= --

/-- A plain set denotes itself: what lets a specification or a guarantee stated at
a representation take a set with no representation at all. -/
instance {α : Type} : ContSet (Set α) α := ⟨id⟩

/-- A matrix denotes itself, read into ℝ by the layer's scalar. What makes a
statement about a set of matrices cover the plain one. -/
instance {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} : ContSet (Mat 𝕋 m n) (Mat ℝ m n) where
  construct M := {toRealMat M}

/-- Left multiplication by a matrix, on matrices. -/
def matMulLeft {p q r : ℕ} (M : Mat ℝ p q) : Mat ℝ q r →ₗ[ℝ] Mat ℝ p r where
  toFun B := M * B
  map_add' := Matrix.mul_add M
  map_smul' c B := Matrix.mul_smul M c B

/-- Right multiplication by a matrix, on matrices. -/
def matMulRight {p q r : ℕ} (M : Mat ℝ q r) : Mat ℝ p q →ₗ[ℝ] Mat ℝ p r where
  toFun B := B * M
  map_add' B C := Matrix.add_mul B C M
  map_smul' c B := Matrix.smul_mul c B M

/-- Matrix multiplication as a bilinear map, which is what a set-valued product
of two matrix representations is taken at. -/
def matMulBilin {p q r : ℕ} : Mat ℝ p q →ₗ[ℝ] Mat ℝ q r →ₗ[ℝ] Mat ℝ p r where
  toFun := matMulLeft
  map_add' A B := LinearMap.ext fun C => Matrix.add_mul A B C
  map_smul' c A := LinearMap.ext fun C => Matrix.smul_mul c A C

/-- A matrix acting on vectors. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q : ℕ} : LinMapSet (Mat 𝕋 p q) (Vec ℝ q) (Vec ℝ p) where
  denote M := {Matrix.mulVecLin (toRealMat M)}

/-- The same matrix acting on matrices, from the left. -/
instance {𝕋 : Type} [Scalar 𝕋] {p q r : ℕ} :
    LinMapSet (Mat 𝕋 p q) (Mat ℝ q r) (Mat ℝ p r) where
  denote M := {matMulLeft (toRealMat M)}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
