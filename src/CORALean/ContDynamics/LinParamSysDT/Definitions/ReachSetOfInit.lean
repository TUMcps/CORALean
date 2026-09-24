import CORALean.ContDynamics.LinParamSysDT.Definitions.WithInput

/-!
# The set reachable from a bare initial set, at every matrix the set holds

`LinParamSysDT` has no `LinearSysDT.reachSet` of its own to read `Reach
.reachExact` off; this is the same recursion, one step's image taken at every
`A ∈ construct sys.sys.A` rather than at a fixed matrix.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in exactly `k` steps from a bare initial set `X`,
under the paired input set and every matrix `sys.sys.A` holds. -/
def LinParamSysDT.WithInput.reachSetOfInit (sys : LinParamSysDT.WithInput 𝕄 S n)
    (X : Set (Vec ℝ n)) : ℕ → Set (Vec ℝ n)
  | 0 => X
  | k + 1 => (⋃ A ∈ construct sys.sys.A, (A *ᵥ ·) '' sys.reachSetOfInit X k) + construct sys.U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
