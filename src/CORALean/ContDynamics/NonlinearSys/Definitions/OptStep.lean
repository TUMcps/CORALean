module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# What `optDeltat` returns

`OptStep`: [1, Alg. 2] line 10's optimal time step size `Δt* = h ζ_δ^{λ'}` of eq. (58), and the
`λ'` it was found at, which line 13 reads again for the gain.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The optimal time step size and the `λ'` it was found at, over the scalar `τ`: `ℝ` for the
exact layer, `𝕋` for a float run. -/
structure NonlinearSys.OptStep (τ : Type) where
  /-- `Δt* = h ζ_δ^{λ'}`, eq. (58). -/
  Δt : τ
  /-- `λ'`, the exponent of `ζ_δ` the cost function was minimised at. -/
  exponent : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
