module

public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep

@[expose] public section

/-!
# One window of `reachWrappingFree`: the set over `τ_k = [t_k, t_k + Δt]`

`R(τ_k) = e^{A t_k} R(τ_0)`: the first window is `timeIntervalStep`, and every
later one is that same set carried forward by the exact flow to `t_k = k Δt`.
The map is taken at `t_k` itself rather than composed `k` times from `e^{AΔt}`,
so a representation that `mtimes` only encloses pays for it once per window,
not once per step before it — the wrapping effect a recursion would compound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`:
`R(τ_k) = e^{A t_k} R(τ_0)`. -/
noncomputable def LinearSys.reachStepkWrappingFree (sys : LinearSys 𝕋 n) (Δt : ℝ) (η : ℕ) (X₀ : S n)
    (k : ℕ) : S n :=
  let tk := (k : ℝ) * Δt                                        -- t_k = k Δt
  let Rτ₀ := sys.timeIntervalStep Δt η X₀                       -- R(τ_0), τ_0 = [0, Δt]
  let eAtk := exp (tk • toRealMat sys.A)                        -- e^{A t_k}
  Mtimes.mtimes eAtk Rτ₀                                        -- R(τ_k) = e^{A t_k} R(τ_0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
