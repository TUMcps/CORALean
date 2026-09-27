import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep

/-!
# One window of `reachUnion`: the homogeneous set over `τ_k = [t_k, t_k + Δt]`

`LinearSys.reachStepkWrappingFree` at a set of matrices: `H^R(τ_k) = e^{A t_k} H^R(τ_0)`,
with `H^R(τ_0)` the step `timeIntervalStep` and `e^{A t_k}` the interval
matrix `expEnclosure` of the box `t_k • sys.A`, applied by one `Mtimes ℐ`.
Taken from the first window rather than from the previous one, as in the point
case, so no window pays for the interval products of those before it.

The matrix a run fixes is the same in every window; the windows here do not
know that, each enclosing its own time range at every member independently —
sound, since a window's set only has to hold that window's states.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The window `τ_k = [k Δt, (k + 1) Δt]` at Taylor order `η`, at every member of
`sys.A`: `H^R(τ_k) = e^{[A] t_k} H^R(τ_0)`. -/
noncomputable def LinParamSys.reachStepk (sys : LinParamSys ℐ n) (Δt : ℝ) (η : ℕ) (X₀ : S n)
    (k : ℕ) : S n :=
  let tk := (k : ℝ) * Δt                                        -- t_k = k Δt
  let HRτ₀ := sys.timeIntervalStep Δt η X₀                      -- H^R(τ_0), τ_0 = [0, Δt]
  let eAtk := sys.expEnclosure tk η                             -- e^{[A] t_k}
  Mtimes.mtimes (𝕄 := ℐ) eAtk HRτ₀                             -- H^R(τ_k) = e^{[A] t_k} H^R(τ_0)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
