module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# What one step of the input contributes, for the support-function verification

The boxes `LinearSys.verifyInputSolutionFloat` returns for a step `Δt` and the input
`u(t) ∈ u₀ + M [-1, 1]^m` of CORA's canonical form: the constant input's solution
`(∫₀^Δt e^{sA} ds) u₀` (CORA's `Pu`), the orders `Δt^{i+1}/(i+1)! Aⁱ M`, `i < η`, of the varying
part (the generators of CORA's `overPU`), their sum (CORA's `underPU` without its remainder) and
the bound of the remainder past them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The input's boxes over one step, for `n` states and `m` input generators. -/
structure LinearSys.VerifyInputSolution (𝕋 : Type) (n m : ℕ) where
  /-- The box of `(∫₀^Δt e^{sA} ds) u₀`, as a column. -/
  w : Interval (Mat 𝕋 n 1)
  /-- The boxes of `Δt^{i+1}/(i+1)! Aⁱ M`, `i < η`. -/
  V : List (Interval (Mat 𝕋 n m))
  /-- The box of their sum. -/
  Vs : Interval (Mat 𝕋 n m)
  /-- The bound of row `l` of the remainder past them, summed over the generators. -/
  ρ : Vec 𝕋 n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
