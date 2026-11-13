module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The matrices a closed-form step shares

The order the series are taken at, the remainder `W` of the input solutions, `[e^{AΔt}]`, `[F]`
and `[G]`: they depend on the system and the step length only, so every step of an error loop
reuses them (`LinearSys.closedFormMatricesFloat` forms them).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- What a step of the system at the step length shares: the order, the remainder `W`, `[e^{AΔt}]`,
`[F]` and `[G]`. -/
structure LinearSys.ClosedFormMatrices (𝕋 : Type) (n : ℕ) where
  /-- The order the series are taken at, raised until the exponential is enclosed. -/
  ηe : ℕ
  /-- The entrywise remainder of the input solutions. -/
  W : Mat 𝕋 n n
  /-- `[e^{AΔt}]`. -/
  eAdt : Interval (Mat 𝕋 n n)
  /-- `[F]`, the correction matrix of the state. -/
  F : Interval (Mat 𝕋 n n)
  /-- `[G]`, the correction matrix of the constant input. -/
  G : Interval (Mat 𝕋 n n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
