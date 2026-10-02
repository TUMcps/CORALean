import CORALean.ContSet.ContSet.ContSet
import CORALean.Global.ExactScalar

/-!
# CORA's `projectHighDim_`: embedding into a higher dimension

`S = I(:, proj) * S`: the selection matrix `I(:, proj)`, whose `k`-th column is the unit vector of
coordinate `proj k`, applied through the set's own `mtimes`. A point is padded with zeros outside
`proj`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `projectHighDim_`: `I = eye(N); S = I(:, proj) * S`. -/
def ContSet.projectHighDim_ (s : S n) (N : ℕ) (proj : Fin n → Fin N) : S N :=
  let E : Mat 𝕋 N n := Matrix.of fun i j => if proj j = i then 1 else 0
  Mtimes.mtimes E s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
