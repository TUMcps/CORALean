module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

@[expose] public section

/-!
# Conjugating by `e^{-At}` is a bijection, so membership transports

Every backward reachable set here is `e^{-At}` applied to a set built forward
from `Xend`, and `e^{-At}` is invertible with inverse `e^{At}` — so `x₀` lies in
the image exactly when `e^{At} x₀` lies in the set. That is the one step which
turns [1, Prop. 3] and [1, Prop. 5] from statements about an image into
statements about the propagated point, and it holds for every `A` and `t`,
singular `A` included.

## Inputs
* `A` – matrix
* `t` – time
* `M` – set
* `x₀` – point

## Hypotheses
* none

## Conclusion
* membership in the image is membership of the propagated point

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x₀` is in the `e^{-At}`-image of `M` exactly when `e^{At} x₀` is in `M`. -/
theorem mem_expNeg_image_iff (A : Mat ℝ n n) (t : ℝ) (M : Set (Vec ℝ n)) (x₀ : Vec ℝ n) :
    x₀ ∈ (exp ((-t) • A)).mulVecLin '' M ↔ exp (t • A) *ᵥ x₀ ∈ M := by -- --- PROOF ---
  have hcomm : Commute (t • A) ((-t) • A) := ((Commute.refl A).smul_left t).smul_right (-t)
  -- `exact` and not `rw`: the goal's `*` resolves through a different instance path
  have hmul : exp (t • A) * exp ((-t) • A) = exp ((t + -t) • A) := by
    rw [add_smul]; exact (exp_add_of_commute hcomm).symm
  have hmul' : exp ((-t) • A) * exp (t • A) = exp ((-t + t) • A) := by
    rw [add_smul]; exact (exp_add_of_commute hcomm.symm).symm
  have h₁ : exp (t • A) * exp ((-t) • A) = 1 := by
    rw [hmul, add_neg_cancel, zero_smul, exp_zero]
  have h₂ : exp ((-t) • A) * exp (t • A) = 1 := by
    rw [hmul', neg_add_cancel, zero_smul, exp_zero]
  constructor
  · rintro ⟨z, hz, rfl⟩
    show exp (t • A) *ᵥ (exp ((-t) • A) *ᵥ z) ∈ M
    rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
    exact hz
  · intro h
    refine ⟨exp (t • A) *ᵥ x₀, h, ?_⟩
    show exp ((-t) • A) *ᵥ (exp (t • A) *ᵥ x₀) = x₀
    rw [Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
