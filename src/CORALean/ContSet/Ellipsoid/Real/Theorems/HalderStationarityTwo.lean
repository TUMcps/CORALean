import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.HalderStationarity

/-!
# Halder's stationarity function for two eigenvalues is a cubic over its denominators

For `d = 2`, [1, Eq. 18] clears its denominators to the cubic of [1, Sec. IV-A.1]:
`∑ᵢ (1 − β²λᵢ)/(1 + βλᵢ) = −p₃(β) / ((1 + βλ₁)(1 + βλ₂))` with
`p₃(β) = 2λ₁λ₂β³ + (λ₁ + λ₂)β² − (λ₁ + λ₂)β − 2`. The positive roots of [1, Eq. 18] are
those of `p₃`.

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. IV-A.1]: for `d = 2`, [1, Eq. 18] is `−p₃(β)` over the denominators. -/
theorem Ellipsoid.halderStationarity_two {l₁ l₂ β : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂)
    (hβ : 0 ≤ β) :
    Ellipsoid.halderStationarity ![l₁, l₂] β
      = -(2 * (l₁ * l₂) * β ^ 3 + (l₁ + l₂) * β ^ 2 - (l₁ + l₂) * β - 2)
        / ((1 + β * l₁) * (1 + β * l₂)) := by -- --- PROOF ---
  have e1 : 1 + β * l₁ ≠ 0 := by positivity
  have e2 : 1 + β * l₂ ≠ 0 := by positivity
  simp only [Ellipsoid.halderStationarity, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
