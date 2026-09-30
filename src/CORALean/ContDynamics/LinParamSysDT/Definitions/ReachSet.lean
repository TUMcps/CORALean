import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

/-!
# The set reachable in `k` steps, at every matrix the set holds

`LinearSysDT.reachSet`'s recursion, one step's image taken at every
`A ∈ construct sys.A` rather than at a fixed matrix: no `reduce`, no enclosure,
and nothing an implementation is free to widen.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSet

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in exactly `k` steps from `R₀` under inputs in `U`, at
every matrix `sys.A` holds. -/
def LinParamSysDT.reachSet (sys : LinParamSysDT 𝕄 n) (R₀ U : S n) : ℕ → Set (Vec ℝ n)
  | 0 => construct R₀
  | k + 1 => (⋃ A ∈ construct sys.A, (A *ᵥ ·) '' sys.reachSet R₀ U k) + construct U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
