module

public import CORALean.ContDynamics.LinearSys.Operations.ReachStepk
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuterAt
public import CORALean.ContDynamics.LinearSys.Theorems.TimePointOuter

@[expose] public section

/-!
# One window of `reach` holds the homogeneous flow over the whole window

At `t ∈ τ_k = [k Δt, (k + 1) Δt]`, `e^{At} = e^{A(t - kΔt)} e^{A k Δt}`: the
inner point `e^{A k Δt} x₀` is in `timePoint Δt X₀ k` by `timePoint_outer`, and
`timeInterval_outer_at` at `s = t - k Δt ∈ [0, Δt]`, run on that set, puts
`e^{As} (e^{A k Δt} x₀) = e^{At} x₀` in `reachStepk Δt η X₀ k =
timeInterval Δt η (timePoint Δt X₀ k)`. The statement is
`reachStepkWrappingFree_outer`'s, word for word.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `η` – Taylor order
* `X₀` – initial set
* `k` – window index
* `t` – time

## Hypotheses
* `hΔt` – step length positive
* `hη` – order at least two
* `hε` – scaled norm small enough for the Taylor order
* `hkt` – time at least the window start
* `htk` – time within the window

## Conclusion
* the exponential image of the initial set lies in the window's set
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-September-2026
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every time of the window
`τ_k`, is in `reachStepk`'s set for it. -/
theorem LinearSys.reachStepk_outer (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {η : ℕ}
    (hη : 2 ≤ η) (hε : ‖Δt • toRealMat sys.A‖ / ((η : ℝ) + 2) < 1) (X₀ : S n) {k : ℕ} {t : ℝ}
    (hkt : (k : ℝ) * Δt ≤ t) (htk : t - k * Δt ≤ Δt) : -- --- CONCL ---
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.reachStepk Δt η X₀ k) := by -- --- PROOF ---
  obtain ⟨m, rfl⟩ : ∃ m, η = m + 2 := ⟨η - 2, by omega⟩
  rintro _ ⟨x₀, hx₀, rfl⟩
  -- `e^{A k Δt} x₀` is in `timePoint Δt X₀ k`
  have hpoint := sys.timePoint_outer Δt X₀ k (Set.mem_image_of_mem _ hx₀)
  -- `timeInterval_outer_at` at `s = t - k Δt ∈ [0, Δt]`, run on that set
  have hstep := sys.timeInterval_outer_at hΔt hε (sys.timePoint Δt X₀ k)
    (t := t - k * Δt) (by linarith) htk (Set.mem_image_of_mem _ hpoint)
  -- `e^{At} = e^{A(t - kΔt)} e^{A k Δt}`, both powers of the same matrix
  have hc : Commute ((t - (k : ℝ) * Δt) • toRealMat sys.A) (((k : ℝ) * Δt) • toRealMat sys.A) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp (t • toRealMat sys.A) *ᵥ x₀
      = exp ((t - (k : ℝ) * Δt) • toRealMat sys.A)
        *ᵥ (exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ x₀) := by
    have h := exp_add_of_commute hc
    have hkey : t - (k : ℝ) * Δt + (k : ℝ) * Δt = t := by ring
    rw [← add_smul, hkey] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x₀) h
  -- `reachStepk Δt (m + 2) X₀ k` is `timeInterval Δt (m + 2) (timePoint Δt X₀ k)`
  show exp (t • toRealMat sys.A) *ᵥ x₀
    ∈ construct (sys.timeInterval Δt (m + 2) (sys.timePoint Δt X₀ k))
  rw [hexp]
  exact hstep

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
