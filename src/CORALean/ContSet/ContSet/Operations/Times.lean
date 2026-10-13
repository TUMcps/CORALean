import CORALean.ContSet.ContSet.ContSet
import CORALean.Global.ExactScalar

/-!
# CORA's `times`: the elementwise product with a vector

`diag(v) * S`, as CORA's `times` has it, through the set's own `mtimes`: nothing here
is specific to a representation.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `times`: `A = diag(v); S = A * S`. -/
def ContSet.times (v : Vec 𝕋 n) (s : S n) : S n :=
  let A : Mat 𝕋 n n := Matrix.diagonal v
  Mtimes.mtimes A s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
