module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# A binomial bound

`[1, Eq. 46]`: `2 (m choose (n - 1)) ≤ 2 (e m / (n - 1))^{n - 1}`, the bound on the
facet count of a zonotope with `m` generators in `ℝⁿ` that makes `polymax` polynomial for a
fixed dimension. With `r = n - 1`: `(m choose r) ≤ m^r / r!`, and `r^r / r! ≤ e^r` is one
term of the exponential series. At `r = 0` both sides are `2`.

## Inputs
* `m` – number of generators
* `r` – chosen count, one less than the dimension

## Hypotheses
* none

## Conclusion
* twice the binomial coefficient is at most twice the power of `e m / r`

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem two_mul_choose_le (m r : ℕ) :
    (2 * (m.choose r : ℝ)) ≤ 2 * (Real.exp 1 * m / r) ^ r := by -- --- PROOF ---
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  -- `r^r / r! ≤ e^r`, so `1 / r! ≤ (e / r)^r`
  have hexp : (r : ℝ) ^ r / r.factorial ≤ Real.exp 1 ^ r := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp _ hrpos.le r
  have hc : (m.choose r : ℝ) ≤ (m : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r m
  have key : (m : ℝ) ^ r / r.factorial ≤ (Real.exp 1 * m / r) ^ r := by
    rw [div_pow, mul_pow, div_le_div_iff₀ hfac (by positivity)]
    rw [div_le_iff₀ hfac] at hexp
    nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) m) r]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
