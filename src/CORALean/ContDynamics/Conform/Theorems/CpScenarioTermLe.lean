module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# The scenario bound (9) gives split conformal prediction its marginal coverage

[1, Sec. 2.3]: (9) bounds `E{η} ≥ 1 - C(n_out + n_θ - 1, n_out)(n_out + n_θ)/(n_m + 1)` and
"reduces to (2) whenever `ε` exceeds the subtracted term, which holds for conformal predictors
with `n_θ = 1` and `n_out` as in (4)": with `n_out = n_m - ⌈(n_m + 1)(1 - ε)⌉ ≥ 0` the term is
`(n_out + 1)/(n_m + 1) ≤ ε`. Only this arithmetic is proved; (9) itself is O'Sullivan et al.'s,
cited, and needs scenario theory, not in Mathlib.

## Inputs
* `nm` – number of calibration points
* `nout` – number of removed outliers
* `ε` – miscoverage level

## Hypotheses
* `h4` – `nout` follows the quantile rule

## Conclusion
* the term subtracted in the scenario bound is at most `ε`

## References

* [1] [L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal Prediction:
      Zonotope-Based Uncertainty Quantification for Regression and Classification Tasks". Journal of
      Machine Learning Research,
      2025.](../../../../../references/2025/luetzow-jmlr-zono-conformal-prediction.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 2.3]: at `n_θ = 1` and `n_out` of (4), the term (9) subtracts is at most `ε`. -/
theorem Conform.cp_scenario_term_le (nm nout : ℕ) (ε : ℝ)
    (h4 : (nout : ℤ) = nm - ⌈((nm : ℝ) + 1) * (1 - ε)⌉) : -- --- CONCL ---
    (Nat.choose (nout + 1 - 1) nout : ℝ) * (nout + 1) / (nm + 1) ≤ ε := by -- --- PROOF ---
  rw [Nat.add_sub_cancel, Nat.choose_self, Nat.cast_one, one_mul,
    div_le_iff₀ (by positivity : (0 : ℝ) < nm + 1)]
  -- `n_out + 1 = n_m + 1 - ⌈(n_m + 1)(1 - ε)⌉ ≤ (n_m + 1) ε`
  have hc : (nout : ℝ) = nm - (⌈((nm : ℝ) + 1) * (1 - ε)⌉ : ℝ) := by exact_mod_cast h4
  have hle := Int.le_ceil (((nm : ℝ) + 1) * (1 - ε))
  rw [hc]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
