import CORALean.ContDynamics.LinearSysDT.Definitions.WithInput

/-!
# `reachSet`, read from a bare initial set

`LinearSysDT.reachSet` starts from `construct R₀` for a representation `R₀`;
`Reach.reachExact` starts from a bare `Set`, which is the only thing it is
handed. Same recursion, so `reachSetOfInit_eq_reachSet` reads the two back as
equal whenever the bare set is `construct R₀`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet Scalar

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in exactly `k` steps from a bare initial set `X`,
under the paired input set. -/
def LinearSysDT.WithInput.reachSetOfInit (sys : LinearSysDT.WithInput 𝕋 S n)
    (X : Set (Vec ℝ n)) : ℕ → Set (Vec ℝ n)
  | 0 => X
  | k + 1 => mulVecLin (toRealMat sys.sys.A) '' sys.reachSetOfInit X k + construct sys.U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
