module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# One restart window of the Krylov trajectory a Krylov verification steps through

CORA.cpp's `KrylovWindow`: along a direction `w`, `z(t) = w' e^{tA}` is `ν V e^{τH} e₁` plus an
error of 2-norm at most `err` at every time `τ ∈ [0, steps Δt₀]` of the window (`Δt₀` its grid),
`V` the basis (`n × k`), `H` the Hessenberg matrix (`k × k`). How the window was built, and its
error bound, are not part of it; `LinearSys.IsVerifyKrylovWindows` states what a list of them must
satisfy.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A window of order `k`: the basis, the Hessenberg matrix, the start vector's norm, the steps of
the pass it covers and the 2-norm bound of its error. -/
structure LinearSys.VerifyKrylovWindow (𝕋 : Type) (n : ℕ) where
  /-- The order of the subspace. -/
  k : ℕ
  /-- The basis, `n × k`. -/
  V : Mat 𝕋 n k
  /-- The Hessenberg matrix, `k × k`. -/
  H : Mat 𝕋 k k
  /-- The norm of the start vector. -/
  ν : 𝕋
  /-- The steps of the grid `Δt₀` the window covers. -/
  steps : ℕ
  /-- The bound of the 2-norm error at every time of the window. -/
  err : 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
