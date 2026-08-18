import CORALean.Global.Tensor

/-!
# The scalar a layer computes in

`Scalar 𝕋` is a type whose matrices denote real ones: ℝ itself, or a machine
scalar read entrywise. It is all the exact layer needs to know about the arithmetic
an implementation actually runs, which is what lets one guarantee cover both.

Global rather than in either layer: it mentions no set representation, and both
layers instantiate it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean

class Scalar (𝕋 : Type) where
  toRealMat {m n : ℕ} : Mat 𝕋 m n → Mat ℝ m n

/-- ℝ stores itself. -/
instance : Scalar ℝ where
  toRealMat M := M

end CORALean
