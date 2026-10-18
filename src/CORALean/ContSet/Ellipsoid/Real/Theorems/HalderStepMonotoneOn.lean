module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStep
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderInvSumPos
public import CORALean.ContSet.Ellipsoid.Real.Theorems.HalderLamSumPos

@[expose] public section

/-!
# Halder's step is monotone

The quotient `∑ 1/(1+βλᵢ) / ∑ λᵢ/(1+βλᵢ)` of [1, Eq. 26] is increasing in `β ≥ 0`.
Cross-multiplying, `A(x) B(y) ≤ A(y) B(x)` for `x ≤ y` is a double sum whose terms pair off
as `−(y − x)(a − b)² / ((1+xa)(1+xb)(1+ya)(1+yb)) ≤ 0`. Monotone and with a unique fixed
point, the step brings every orbit to it ([1, Thm. 3]).

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_pair {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hxy : x ≤ y) : -- --- STMT ---
    (1 / (1 + x * a) * (b / (1 + y * b)) - 1 / (1 + y * a) * (b / (1 + x * b)))
    + (1 / (1 + x * b) * (a / (1 + y * a)) - 1 / (1 + y * b) * (a / (1 + x * a)))
    ≤ 0 := by -- --- PROOF ---
  -- the four denominators are positive, in both orders of the factors
  have h1 : 0 < 1 + x * a := by positivity
  have h2 : 0 < 1 + x * b := by positivity
  have h3 : 0 < 1 + y * a := by nlinarith
  have h4 : 0 < 1 + y * b := by nlinarith
  -- the sum of the two terms is `−(y − x)(a − b)²` over the denominators
  have : (1 / (1 + x * a) * (b / (1 + y * b)) - 1 / (1 + y * a) * (b / (1 + x * b)))
    + (1 / (1 + x * b) * (a / (1 + y * a)) - 1 / (1 + y * b) * (a / (1 + x * a)))
    = -((y - x) * (a - b) ^ 2) / ((1 + x * a) * (1 + x * b) * (1 + y * a) * (1 + y * b)) := by
    have e1 : 1 + a * x ≠ 0 := by positivity
    have e2 : 1 + b * x ≠ 0 := by positivity
    have e3 : 1 + a * y ≠ 0 := by nlinarith
    have e4 : 1 + b * y ≠ 0 := by nlinarith
    have e5 : 1 + x * a ≠ 0 := h1.ne'
    have e6 : 1 + x * b ≠ 0 := h2.ne'
    have e7 : 1 + y * a ≠ 0 := h3.ne'
    have e8 : 1 + y * b ≠ 0 := h4.ne'
    field_simp
    ring
  rw [this]
  have hn : 0 ≤ (y - x) * (a - b) ^ 2 := mul_nonneg (sub_nonneg.2 hxy) (sq_nonneg (a - b))
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem Ellipsoid.aux_cross_le (hlam : ∀ i, 0 < lam i) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Ellipsoid.halderInvSum lam x * Ellipsoid.halderLamSum lam y
      ≤ Ellipsoid.halderInvSum lam y * Ellipsoid.halderLamSum lam x := by -- --- PROOF ---
  unfold Ellipsoid.halderInvSum Ellipsoid.halderLamSum
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_nonpos, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  -- the double sum of `F`, whose symmetrised terms are nonpositive
  let F : ι → ι → ℝ := fun i j =>
    1 / (1 + x * lam i) * (lam j / (1 + y * lam j)) -
      1 / (1 + y * lam i) * (lam j / (1 + x * lam j))
  have hpair : ∀ i j, F i j + F j i ≤ 0 := fun i j =>
    Ellipsoid.aux_pair (hlam i) (hlam j) hx hxy
  have hsw : ∑ i, ∑ j, F i j = ∑ i, ∑ j, F j i := Finset.sum_comm
  -- twice the double sum is the double sum of the symmetrised terms, which are nonpositive
  have : 2 * ∑ i, ∑ j, F i j ≤ 0 := by
    calc 2 * ∑ i, ∑ j, F i j = ∑ i, ∑ j, F i j + ∑ i, ∑ j, F j i := by rw [← hsw]; ring
      _ = ∑ i, ∑ j, (F i j + F j i) := by simp [Finset.sum_add_distrib]
      _ ≤ 0 := Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => hpair i j
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- The step [1, Eq. 26] is monotone on `[0, ∞)`, the fact [1, Thm. 3] iterates on. -/
theorem Ellipsoid.halderStep_monotoneOn [Nonempty ι] (hlam : ∀ i, 0 < lam i) :
    MonotoneOn (Ellipsoid.halderStep lam) (Set.Ici 0) := by -- --- PROOF ---
  intro x hx y hy hxy
  unfold Ellipsoid.halderStep
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ (Ellipsoid.halderLamSum_pos hlam hx) (Ellipsoid.halderLamSum_pos hlam hy)]
  exact Ellipsoid.aux_cross_le hlam hx hxy

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
