import CORALean.Global.Scalar

/-!
# Matrix-like types, as the matrices they stand for

`denote` is to matrices what `construct` is to set representations: a plain
matrix stands for itself, an interval matrix for everything between its bounds.
An operation stated against this covers both, and the plain case is the
singleton, so nothing is weakened by phrasing it here.

Keyed on the shape `ℕ → ℕ → Type` rather than on matrices as such, so widening
this to tensors later adds an instance instead of replacing the class.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

variable {𝕋 : Type}

class MatSet (𝕄 : ℕ → ℕ → Type) where
  denote {m n : ℕ} : 𝕄 m n → Set (Mat ℝ m n)

/-- A matrix denotes itself, read into ℝ by the layer's scalar. -/
instance [Scalar 𝕋] : MatSet (Mat 𝕋) where
  denote M := {Scalar.toRealMat M}

@[simp] theorem MatSet.denote_mat [Scalar 𝕋] {m n : ℕ} (M : Mat 𝕋 m n) :
    MatSet.denote M = {Scalar.toRealMat M} := rfl

end CORALean
