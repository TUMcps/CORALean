import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter

/-!
# `timeIntervalStep` encloses the exact reachable set of the step

`timeIntervalStep_outer_at`, quantified over the step's own time domain
`[0, Δt]` in one statement, through `reachExact`, and at the Taylor order `η`
itself rather than the `m + 2` it is admissible written as:
`reachExact Δt (construct X₀)` is exactly the union over `t ∈ [0, Δt]` of the
image of `construct X₀` under `exp (t • A)`, so unpacking one `t` and its
bounds from membership, and `η`'s own `m + 2` witness from `2 ≤ η`, is all
this adds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
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
variable [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

omit [∀ n, Reduce (S n) (Vec ℝ n)] in
/-- The exact reachable set of the step, `reachExact Δt`, is inside
`timeIntervalStep`'s, at the order `η` itself. -/
theorem LinearSys.timeIntervalStep_outer (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {η : ℕ}
    (hη : 2 ≤ η) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (X₀ : S n) :
    sys.reachExact Δt (construct X₀)
      ⊆ construct (sys.timeIntervalStep Δt η X₀) := by
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 2 := ⟨η - 2, by omega⟩
  rintro _ ⟨t, ⟨ht0, htr⟩, x₀, hx₀, rfl⟩
  exact sys.timeIntervalStep_outer_at hΔt hε X₀ ht0 htr (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
