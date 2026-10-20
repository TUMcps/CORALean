module

public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# The binomial tail falls with the success probability

A step of [1, Thm. 3]'s proof (Appendix B): `Σ_{i=0}^k C(m, i) ζⁱ(1 - ζ)^{m-i}`, the probability
of at most `k` successes in `m` independent trials of probability `ζ`, is strictly decreasing in
`ζ ∈ [0, 1]` when `k < m`, "as it can be checked by differentiation". The sum is that of the
Bernstein polynomials `b_{m,i}`, `i ≤ k`, whose derivatives telescope to `-m b_{m-1,k}`, negative
on `(0, 1)`.

## Inputs
* `m` – number of trials
* `k` – largest number of successes counted

## Hypotheses
* `hk` – fewer successes counted than trials

## Conclusion
* the binomial tail is strictly decreasing in the success probability on the unit interval

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Polynomial


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- the derivatives of the first `k + 1` Bernstein polynomials telescope
theorem aux_derivative_sum_bernstein (m k : ℕ) :
    derivative (∑ i ∈ Finset.range (k + 1), bernsteinPolynomial ℝ m i) =
      -(m : ℝ[X]) * bernsteinPolynomial ℝ (m - 1) k := by -- --- PROOF ---
  induction k with
  | zero => simp [bernsteinPolynomial.derivative_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, derivative_add, ih, bernsteinPolynomial.derivative_succ]
    ring

-- the sum is the polynomial's value
theorem aux_eval_sum_bernstein (m k : ℕ) (p : ℝ) :
    (∑ i ∈ Finset.range (k + 1), bernsteinPolynomial ℝ m i).eval p =
      ∑ i ∈ Finset.range (k + 1), (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i) := by
  simp [eval_finsetSum, bernsteinPolynomial]


-- =======================================  MAIN THEOREM  ======================================= --

theorem binomialTail_strictAntiOn {m k : ℕ} (hk : k < m) :
    StrictAntiOn (fun p : ℝ => ∑ i ∈ Finset.range (k + 1),
      (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i)) (Set.Icc 0 1) := by -- --- PROOF ---
  set q := ∑ i ∈ Finset.range (k + 1), bernsteinPolynomial ℝ m i
  have hfun : (fun p : ℝ => ∑ i ∈ Finset.range (k + 1),
      (m.choose i : ℝ) * p ^ i * (1 - p) ^ (m - i)) = fun p => q.eval p := by
    funext p; exact (aux_eval_sum_bernstein m k p).symm
  rw [hfun]
  refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) q.continuousOn fun x hx => ?_
  rw [interior_Icc] at hx
  -- the derivative is `-m C(m-1, k) xᵏ (1 - x)^{m-1-k}`, negative inside
  rw [Polynomial.deriv, aux_derivative_sum_bernstein]
  have hc : (0 : ℝ) < ((m - 1).choose k : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have h1 : 0 < x ^ k := pow_pos hx.1 k
  have h2 : 0 < (1 - x) ^ (m - 1 - k) := pow_pos (by linarith [hx.2]) _
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  simp only [eval_mul, eval_neg, eval_natCast, bernsteinPolynomial, eval_pow, eval_sub, eval_one,
    eval_X]
  have := mul_pos (mul_pos (mul_pos hm hc) h1) h2
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
