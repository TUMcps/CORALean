module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# CORA's `taylorMatrices`: the remainder and the two correction matrices

The remainder `E(Δt,η)` of the exponential, entry by entry, and the correction matrices `[F]` of the
state and `[G]` of the constant input at the order `η` of the step
(`LinearSys.taylorMatricesFloat` forms them).
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- CORA's `[E, F, G] = taylorMatrices(linsys, Δt, η)`, `E` as the bound `W` of its entries. -/
structure LinearSys.TaylorMatrices (𝕋 : Type) (n : ℕ) where
  /-- The bound of the entrywise remainder, `E = [−W, W]`. -/
  W : Mat 𝕋 n n
  /-- `[F]`, the correction matrix of the state. -/
  F : Interval (Mat 𝕋 n n)
  /-- `[G]`, the correction matrix of the constant input. -/
  G : Interval (Mat 𝕋 n n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
