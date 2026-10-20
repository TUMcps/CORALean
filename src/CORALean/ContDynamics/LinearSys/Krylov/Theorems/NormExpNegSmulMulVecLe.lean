module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.NormExpSmulMulVecLe

@[expose] public section

/-!
# A matrix with `Re(x*Ax) ≥ ν‖x‖²` gives `‖e^{-rA}x‖₂ ≤ e^{-rν}‖x‖₂`

[1, Eq. 3.5], `‖e^{tA}‖ ≤ e^{tµ(A)}` for the logarithmic norm `µ(A)`, bounds in Thm. 3.1
`‖e^{(t-τ)A}‖ = ‖e^{(τ-t)(-A)}‖ ≤ e^{(t-τ)ν(A)}`, `ν(A) = min Re W(A)`. Here for any complex `A`
and real `ν` with `Re(x*Ax) ≥ ν x*x` for all `x`
(`ν = ν(A)` is the largest such `ν`), on a vector and for `r ≥ 0`: `-A + ν` has its field of
values in the closed left half-plane, so `e^{r(-A+ν)}` does not increase the Euclidean norm
(`Krylov.norm_exp_smul_mulVec_le`), and `e^{r(-A+ν)} = e^{rν}e^{-rA}`. `‖·‖₂` is the norm of
`EuclideanSpace ℂ (Fin n)`, reached by `WithLp.toLp 2`.

## Inputs
* `A` – matrix
* `ν` – lower bound on the field of values
* `x` – vector
* `r` – time

## Hypotheses
* `hA` – real part of the Rayleigh quotient at least the lower bound
* `hr` – time nonnegative

## Conclusion
* the norm of the exponential image is at most the decayed norm

## References

* [1] H. Wang, Q. Ye. "Error bounds for the Krylov subspace methods for computations of matrix
  exponentials". SIAM Journal on Matrix Analysis and Applications, 38(1):155-187, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 3.5]: `ν x*x ≤ Re(x*Ax)` for all `x` gives `‖e^{r(-A)}x‖₂ ≤ e^{-rν}‖x‖₂` for
`r ≥ 0`. -/
theorem Krylov.norm_exp_neg_smul_mulVec_le (A : Mat ℂ n n) (ν : ℝ)
    (hA : ∀ x : Fin n → ℂ, ν * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (A *ᵥ x)).re) (x : Fin n → ℂ)
    {r : ℝ} (hr : 0 ≤ r) : -- --- CONCL ---
    ‖(WithLp.toLp 2 (exp (r • (-A)) *ᵥ x) : EuclideanSpace ℂ (Fin n))‖ ≤
      Real.exp (-(r * ν)) * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖ := by -- --- PROOF ---
  set N : Mat ℂ n n := -A + ((ν : ℂ)) • 1 with hN
  -- `-A + ν` has `Re(y*Ny) ≤ 0`
  have hNneg : ∀ y : Fin n → ℂ, (star y ⬝ᵥ (N *ᵥ y)).re ≤ 0 := by
    intro y
    have h := hA y
    have : (star y ⬝ᵥ (N *ᵥ y)).re = -(star y ⬝ᵥ (A *ᵥ y)).re + ν * (star y ⬝ᵥ y).re := by
      simp [hN, Matrix.add_mulVec, Matrix.neg_mulVec, dotProduct_add, dotProduct_neg,
        Matrix.smul_mulVec, dotProduct_smul]
    linarith
  have hcon := Krylov.norm_exp_smul_mulVec_le N hNneg x hr
  -- `e^{rN} = e^{r(-A)} · e^{rν}`
  have hrN : r • N = r • (-A) + ((r * ν : ℝ) : ℂ) • (1 : Mat ℂ n n) := by
    rw [hN, smul_add]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h]
  -- the scalar part commutes, and its exponential is `e^{rν}`
  have hcomm : Commute (r • (-A)) (((r * ν : ℝ) : ℂ) • (1 : Mat ℂ n n)) :=
    (Commute.one_right _).smul_right _
  have hscal : exp (((r * ν : ℝ) : ℂ) • (1 : Mat ℂ n n)) =
      ((Real.exp (r * ν) : ℝ) : ℂ) • (1 : Mat ℂ n n) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
    ext i j
    by_cases h : i = j
    · simp [h, Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
    · simp [h]
  -- hence `e^{rN}x = e^{rν} e^{r(-A)}x`
  have hexp : exp (r • N) *ᵥ x = ((Real.exp (r * ν) : ℝ) : ℂ) • (exp (r • (-A)) *ᵥ x) := by
    rw [hrN, Matrix.exp_add_of_commute _ _ hcomm, hscal, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mulVec]
  -- the contraction bound, scaled back by `e^{-rν}`
  rw [hexp, WithLp.toLp_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    at hcon
  have hpos := Real.exp_pos (r * ν)
  have h2 : Real.exp (-(r * ν)) * Real.exp (r * ν) = 1 := by
    rw [← Real.exp_add]; simp
  calc _ = Real.exp (-(r * ν)) * (Real.exp (r * ν) * ‖(WithLp.toLp 2 (exp (r • (-A)) *ᵥ x) :
        EuclideanSpace ℂ (Fin n))‖) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcon (Real.exp_pos _).le

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
