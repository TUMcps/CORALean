import CORALean.ContDynamics.LinearSysDT.Definitions.ReachSet

/-!
# The exact set `Reach LinearSysDT` is asked to enclose

Every state reachable in at most `K` steps from `R₀` under inputs in `U`: `reachSet`
at each step, united. Positional, as the mathematics: `Reach` reads `R₀`, `U` and
`K = tFinal - tStart` off `params`, the system being time-invariant.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every state reachable in at most `K` steps from `R₀` under inputs in `U`. -/
def LinearSysDT.reachUnionExact (sys : LinearSysDT 𝕋 n) (R₀ U : S n) (K : ℕ) : Set (Vec ℝ n) :=
  ⋃ k ≤ K, sys.reachSet R₀ U k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
