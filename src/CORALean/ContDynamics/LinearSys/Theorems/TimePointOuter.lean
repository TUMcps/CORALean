module

public import CORALean.ContDynamics.LinearSys.Operations.TimePoint
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# `timePoint` holds the homogeneous flow at its own sample time

By induction on `k`: point `0` is `X₀` itself, at `e^{A · 0} = I`; at
`k + 1`, `e^{A(k+1)Δt} = e^{AΔt} e^{AkΔt}`, both powers of the same matrix, so
the inductive hypothesis's point at `kΔt` carries to `(k+1)Δt` by
`mtimes_outer`, the same step `timePoint` itself takes — the sample-time half
of [1, Alg. 1]'s own recursion, `reachStepk_outer` the window it encloses from
each one.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `X₀` – initial set
* `k` – step index

## Hypotheses
* none

## Conclusion
* the exponential image of the initial set lies in the time-point set

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
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
variable [Mtimes (Mat ℝ) S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at the sample time `k Δt`,
is in `timePoint`'s set for it. -/
theorem LinearSys.timePoint_outer (sys : LinearSys 𝕋 n) (Δt : ℝ) (X₀ : S n)
    (k : ℕ) : -- --- CONCL ---
    (fun x₀ => exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.timePoint Δt X₀ k) := by -- --- PROOF ---
  induction k with
  | zero =>
    -- `e^{A · 0} = I`, so the image at point `0` is `X₀` itself
    rintro _ ⟨x₀, hx₀, rfl⟩
    simp only [Nat.cast_zero, zero_mul, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec]
    exact hx₀
  | succ k ih =>
    rintro _ ⟨x₀, hx₀, rfl⟩
    -- `(k + 1) Δt = Δt + k Δt`, both powers of the same matrix
    have hc : Commute ((Δt : ℝ) • toRealMat sys.A) (((k : ℝ) * Δt) • toRealMat sys.A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have hexp : exp ((((k + 1 : ℕ) : ℝ) * Δt) • toRealMat sys.A) *ᵥ x₀
        = exp (Δt • toRealMat sys.A) *ᵥ (exp (((k : ℝ) * Δt) • toRealMat sys.A) *ᵥ x₀) := by
      have h := exp_add_of_commute hc
      rw [← add_smul] at h
      have hkey : (((k + 1 : ℕ) : ℝ) * Δt) = Δt + (k : ℝ) * Δt := by push_cast; ring
      rw [hkey, Matrix.mulVec_mulVec]
      exact congrArg (· *ᵥ x₀) h
    show exp ((((k + 1 : ℕ) : ℝ) * Δt) • toRealMat sys.A) *ᵥ x₀
      ∈ construct (Mtimes.mtimes _ _)
    rw [hexp]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ (ih
      (Set.mem_image_of_mem _ hx₀))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
