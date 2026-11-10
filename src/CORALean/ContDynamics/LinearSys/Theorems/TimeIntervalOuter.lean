module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterOfSubset
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointOneOuter

@[expose] public section

/-!
# `timeInterval` encloses the exact reachable set of the step

`timeInterval_outer_of_subset` with the end set the time-point set `timePoint Δt Xₖ 1`, which
`timePoint_one_outer` shows holds the image of `Xₖ`: the statement a caller with no end set in
hand wants, the same step `reach` takes between consecutive time points.
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
/-- The exact reachable set of the step, `reachExact Δt`, is inside `timeInterval`'s, at the
order `η` itself, where `Xₖ₁` is the time-point set `timePoint Δt Xₖ 1`. -/
theorem LinearSys.timeInterval_outer (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {η : ℕ}
    (hη : 2 ≤ η) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (Xₖ Xₖ₁ : S n)
    (hX : Xₖ₁ = sys.timePoint Δt Xₖ 1) : -- --- CONCL ---
    sys.reachExact Δt (toSet Xₖ)
      ⊆ toSet (sys.timeInterval Δt η Xₖ Xₖ₁) := by -- --- PROOF ---
  subst hX
  exact sys.timeInterval_outer_of_subset hΔt hη hε Xₖ _ (sys.timePoint_one_outer Δt Xₖ)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
