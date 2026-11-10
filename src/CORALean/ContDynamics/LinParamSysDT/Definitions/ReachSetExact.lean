module

public import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT

@[expose] public section

/-!
# The set reachable in `k` steps, at every matrix the set holds

`LinearSysDT.reachSetExact`'s recursion, one step's image taken at every
`A ∈ toSet sys.A` rather than at a fixed matrix: no `reduce`, no enclosure,
and nothing an implementation is free to widen.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set

## Output
* the states reachable in exactly `k` steps, by step count
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise ContSetLike

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSetLike (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSetLike (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in exactly `k` steps from `R₀` under inputs in `U`, at
every matrix `sys.A` holds. -/
def LinParamSysDT.reachSetExact (sys : LinParamSysDT 𝕄 n) (R₀ U : S n) : ℕ → Set (Vec ℝ n)
  | 0 => toSet R₀
  | k + 1 => (⋃ A ∈ toSet sys.A, (A *ᵥ ·) '' sys.reachSetExact R₀ U k) + toSet U

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
