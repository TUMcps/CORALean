module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity

@[expose] public section

/-!
# Halder's stationarity function is strictly decreasing

Each term `(1 − β²λ)/(1 + βλ)` of [1, Eq. 18] is strictly decreasing in `β ≥ 0`: for
`a < b` the difference of the numerators over the common denominator is
`(b − a) λ (1 + (a + b) + abλ) > 0`. A sum of strictly decreasing terms is, so the root of
[1, Thm. 2] is unique.

## Inputs
* none

## Hypotheses
* `hlam` – every `λᵢ` positive

## Conclusion
* the stationarity function is strictly decreasing on `[0, ∞)`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {ι : Type*} [Fintype ι]
variable {lam : ι → ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_term_lt {l a b : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hab : a < b) :
    (1 - b ^ 2 * l) / (1 + b * l) < (1 - a ^ 2 * l) / (1 + a * l) := by -- --- PROOF ---
  have h1 : 0 < 1 + a * l := by positivity
  have h2 : 0 < 1 + b * l := by nlinarith
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith [mul_pos hl (sub_pos.2 hab), mul_pos (mul_pos hl hl) (sub_pos.2 hab),
    mul_nonneg ha hl.le, mul_nonneg (mul_nonneg ha hl.le) (sub_pos.2 hab).le,
    mul_pos (mul_pos hl (sub_pos.2 hab)) (add_pos_of_nonneg_of_pos ha (lt_of_le_of_lt ha hab)),
    mul_nonneg (mul_nonneg ha (sub_pos.2 hab).le) (mul_nonneg hl.le hl.le)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The left side of [1, Eq. 18] is strictly decreasing on `[0, ∞)`, as [1, Thm. 2] needs. -/
theorem Ellipsoid.halderStationarity_strictAntiOn [Nonempty ι] (hlam : ∀ i, 0 < lam i) :
    StrictAntiOn (Ellipsoid.halderStationarity lam) (Set.Ici 0) := by
  intro a ha b hb hab
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
    Ellipsoid.aux_term_lt (hlam i) ha hab

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
