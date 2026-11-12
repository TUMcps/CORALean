module

public import CORALean.Global.EuclideanNorm
public import CORALean.Global.Tensor
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# The weighted quadratic form of `e^{tA}x` grows at most by `e^{2μt}`

[1, Eq. 3.4] bounds `‖e^{tA}‖₂ ≤ e^{tμ}` by the quadratic form `x*Ax ≤ μ x*x`, and Gershgorin's
bound of that form is large for a stable but non-normal `A`. A Lyapunov weight `P` measures the same
growth sharply: if `x*PAx ≤ μ x*Px`, i.e. `A*P + PA ≼ 2μP`, then `y(t) = e^{tA}x` has `d/dt y*Py =
2 y*PAy ≤ 2μ y*Py`, so `y(t)*Py(t) ≤ e^{2μt} x*Px`. `μ` may be negative.

## Inputs
* `A` – matrix
* `P` – symmetric weight
* `μ` – growth rate in the weight
* `x` – start vector
* `t` – time

## Hypotheses
* `hS` – weight symmetric
* `hPA` – `x*PAx ≤ μ x*Px`
* `ht` – time nonnegative

## Conclusion
* the weighted quadratic form grows by at most `e^{2μt}`

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `d/ds e^{sM}x = Me^{sM}x` for a real matrix. -/
private theorem aux_hasDerivAt_exp (M : Mat ℝ n n) (x : Vec ℝ n) (s : ℝ) : -- --- CONCL ---
    HasDerivAt (fun r : ℝ => exp (r • M) *ᵥ x) (M *ᵥ (exp (s • M) *ᵥ x)) s := by -- --- PROOF ---
  -- `B ↦ Bx` as a continuous linear map
  let L : Mat ℝ n n →ₗ[ℝ] Vec ℝ n :=
    { toFun := fun B => B *ᵥ x
      map_add' := fun B C => Matrix.add_mulVec B C x
      map_smul' := fun r B => by rw [Matrix.smul_mulVec, RingHom.id_apply] }
  have h := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) M s)
  have h2 : HasDerivAt (fun r : ℝ => exp (r • M) *ᵥ x)
      ((LinearMap.toContinuousLinearMap L) (M * exp (s • M))) s := h
  refine h2.congr_deriv ?_
  show (M * exp (s • M)) *ᵥ x = _
  rw [Matrix.mulVec_mulVec]

/-- The product rule for the quadratic form `y*Py`. -/
private theorem aux_quad_deriv (P : Mat ℝ n n) (y y' : ℝ → Vec ℝ n) (s : ℝ)
    (h : HasDerivAt y (y' s) s) : -- --- CONCL ---
    HasDerivAt (fun r => y r ⬝ᵥ (P *ᵥ y r))
      (y' s ⬝ᵥ (P *ᵥ y s) + y s ⬝ᵥ (P *ᵥ y' s)) s := by -- --- PROOF ---
  -- the entries of `y` and `Py`, then the sum of their products
  have hc : ∀ i, HasDerivAt (fun r => y r i) (y' s i) s := fun i => (hasDerivAt_pi.1 h) i
  have hPy : ∀ i, HasDerivAt (fun r => (P *ᵥ y r) i) ((P *ᵥ y' s) i) s := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hc j).const_mul (P i j)
  have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).mul (hPy i)
  refine this.congr_deriv ?_
  simp only [dotProduct, ← Finset.sum_add_distrib]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x*PAx ≤ μ x*Px` for symmetric `P` gives `(e^{tA}x)*P(e^{tA}x) ≤ e^{2μt} x*Px` for `t ≥ 0`. -/
theorem Krylov.quad_exp_le_weighted (A P : Mat ℝ n n) (μ : ℝ) (hS : Pᵀ = P)
    (hPA : ∀ x, x ⬝ᵥ (P *ᵥ (A *ᵥ x)) ≤ μ * (x ⬝ᵥ (P *ᵥ x))) (x : Vec ℝ n) {t : ℝ}
    (ht : 0 ≤ t) : -- --- CONCL ---
    (exp (t • A) *ᵥ x) ⬝ᵥ (P *ᵥ (exp (t • A) *ᵥ x)) ≤
      Real.exp (2 * μ * t) * (x ⬝ᵥ (P *ᵥ x)) := by -- --- PROOF ---
  set y : ℝ → Vec ℝ n := fun r => exp (r • A) *ᵥ x with hy
  set f : ℝ → ℝ := fun r => y r ⬝ᵥ (P *ᵥ y r) with hf
  -- a symmetric weight makes the form symmetric
  have hsym : ∀ u v : Vec ℝ n, u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := fun u v => by
    rw [dotProduct_comm, ← vecMul_transpose, hS, ← dotProduct_mulVec]
  -- `f' = 2 y*PAy`
  have hd : ∀ r, HasDerivAt f (2 * (y r ⬝ᵥ (P *ᵥ (A *ᵥ y r)))) r := fun r => by
    have h := aux_quad_deriv P y (fun r => A *ᵥ y r) r (aux_hasDerivAt_exp A x r)
    refine h.congr_deriv ?_
    rw [hsym (A *ᵥ y r) (y r)]
    ring
  -- `e^{-2μr} f(r)` does not increase
  have hg : ∀ r, HasDerivAt (fun r => Real.exp (-(2 * μ) * r) * f r)
      (Real.exp (-(2 * μ) * r) * (2 * (y r ⬝ᵥ (P *ᵥ (A *ᵥ y r))) - 2 * μ * f r)) r := fun r => by
    have h0 : HasDerivAt (fun r : ℝ => -(2 * μ) * r) (-(2 * μ)) r := by
      simpa using (hasDerivAt_id r).const_mul (-(2 * μ))
    have h1 : HasDerivAt (fun r : ℝ => Real.exp (-(2 * μ) * r))
        (Real.exp (-(2 * μ) * r) * (-(2 * μ))) r := (Real.hasDerivAt_exp _).comp r h0
    refine (h1.mul (hd r)).congr_deriv ?_
    ring
  have hanti : Antitone fun r => Real.exp (-(2 * μ) * r) * f r :=
    antitone_of_deriv_nonpos (fun r => (hg r).differentiableAt) fun r => by
      rw [(hg r).deriv]
      have := hPA (y r)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by simp only [hf]; linarith)
  have h := hanti ht
  simp only [hy, hf, zero_smul, exp_zero, one_mulVec, mul_zero, Real.exp_zero, one_mul] at h
  have h2 : Real.exp (2 * μ * t) * Real.exp (-(2 * μ) * t) = 1 := by
    rw [← Real.exp_add]; simp
  -- scaled back by `e^{2μt}`
  calc _ = Real.exp (2 * μ * t) * (Real.exp (-(2 * μ) * t) *
        ((exp (t • A) *ᵥ x) ⬝ᵥ (P *ᵥ (exp (t • A) *ᵥ x)))) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
