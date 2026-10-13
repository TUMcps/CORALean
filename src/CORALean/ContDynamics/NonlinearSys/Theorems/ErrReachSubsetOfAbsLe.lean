module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The condition that does keep the error set inside `[-θ r, θ r]`

[1, Eq. 7] wants `R̄err(r) = N [-L̂, L̂] ⊆ [-θ r, θ r]`, `N := A⁻¹(e^{Ar} - I)`, and
offers `L̂ ≤ |N⁻¹| θ r` for it, which `admissibleLinError_not_sufficient` refutes.
The test that works is on `N` itself, not on its inverse: the box `[-L̂, L̂]` is
mapped into the box of radius `|N| L̂`, so `|N| L̂ ≤ θ r` suffices, coordinate by
coordinate, `|(N x)ᵢ| ≤ Σⱼ |Nᵢⱼ| |xⱼ| ≤ Σⱼ |Nᵢⱼ| L̂ⱼ`. It needs no inverse of `A` or
of `e^{Ar} - I` to be checked.

`N` is whatever the caller passes as `A⁻¹(e^{Ar} - I)`: the statement holds for every
matrix, so `A⁻¹` is Mathlib's, zero at a singular `A`, without affecting it. The
formula `R̄err(r) = A⁻¹(e^{Ar} - I)[-L̂, L̂]` is the paper's, quoted from an
earlier paper of its authors, and taken as given here.

Real only: a specification, with nothing to compute.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 7], corrected: `|A⁻¹(e^{Ar} - I)| L̂ ≤ θ r` puts `A⁻¹(e^{Ar} - I)[-L̂, L̂]`
inside `[-θ r, θ r]`. -/
theorem NonlinearSys.errReach_subset_of_abs_le (A : Mat ℝ n n) (r : ℝ) (θ L : Vec ℝ n)
    (h : ∀ i, (Real.MatExp.absMat (A⁻¹ * (NormedSpace.exp (r • A) - 1)) *ᵥ L) i ≤ (r • θ) i) :
    (fun x => (A⁻¹ * (NormedSpace.exp (r • A) - 1)) *ᵥ x) ''
        (⟨-L, L⟩ : Real.Interval (Vec ℝ n)).construct
      ⊆ (⟨-(r • θ), r • θ⟩ : Real.Interval (Vec ℝ n)).construct := by -- --- PROOF ---
  set N : Mat ℝ n n := A⁻¹ * (NormedSpace.exp (r • A) - 1)
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : ∀ j, |x j| ≤ L j := fun j => by
    have h' : -L j ≤ x j ∧ x j ≤ L j := hx j
    exact abs_le.mpr h'
  -- each row of `N x` is bounded by the same row of `|N| L̂`
  have hrow : |(N *ᵥ x) i| ≤ (Real.MatExp.absMat N *ᵥ L) i := by
    simp only [Matrix.mulVec, dotProduct, Real.MatExp.absMat]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx' j) (abs_nonneg _)
  change -(r • θ) i ≤ (N *ᵥ x) i ∧ (N *ᵥ x) i ≤ (r • θ) i
  exact abs_le.mp (hrow.trans (h i))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
