module

public import CORALean.ContDynamics.LinParamSysDT.Definitions.ReachSetExact

@[expose] public section

/-!
# The exact set `Reach LinParamSysDT` is asked to enclose

Every state reachable in at most `K` steps from `R₀` under inputs in `U`, at every
matrix the set holds. Positional, as the mathematics: `Reach` reads `R₀`, `U` and
`K = tFinal - tStart` off `params`, the system being time-invariant.

## Inputs
* `sys` – system
* `R₀` – initial set
* `U` – input set
* `K` – step bound

## Output
* the states reachable in at most `K` steps
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `K` steps from `R₀` under inputs in `U`. -/
def LinParamSysDT.reachUnionExact (sys : LinParamSysDT 𝕄 n) (R₀ U : S n) (K : ℕ) :
    Set (Vec ℝ n) :=
  ⋃ k ≤ K, sys.reachSetExact R₀ U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
