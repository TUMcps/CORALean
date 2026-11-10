module

public import CORALean.ContDynamics.LinearSys.Theorems.TimePointOuter

@[expose] public section

/-!
# `timePoint` at one step holds the flow at `Δt`

`timePoint_outer` at `k = 1`, stated with `Δt` rather than `1 * Δt`: the hypothesis `hX` of
`timeInterval_outer` and `timeInterval_outer_at` for a caller that hands `timeInterval` the set
`timePoint Δt X₀ 1` as the end of its step.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `X₀` – initial set

## Hypotheses
* none

## Conclusion
* the exact set at `Δt` lies in the time-point set after one step
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-November-2026
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
variable [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The exact set at `Δt` is in the time-point set after one step. -/
theorem LinearSys.timePoint_one_outer (sys : LinearSys 𝕋 n) (Δt : ℝ) (X₀ : S n) :
    sys.reachExactAt Δt (toSet X₀) ⊆ toSet (sys.timePoint Δt X₀ 1) := by
  simpa using sys.timePoint_outer Δt X₀ 1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
