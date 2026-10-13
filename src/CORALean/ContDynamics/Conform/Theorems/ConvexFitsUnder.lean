import CORALean.ContDynamics.Conform.Definitions.ZonoConformal
import Mathlib.Analysis.Convex.Basic

/-!
# A data point's containment constraint is convex in the stretch factors

The constraint (19c)-(19e), or (20c)-(20e), of one data point, with its `βₘ` eliminated, is
`FitsUnder C α`: some `β` in the point's convex set `C` with `|β| ≤ α`. It is convex in `α`,
which is what makes (19) and (20) convex scenario programs in `α` ([1, Sec. 5.2]); the
probability bounds (8) and (9) applied to them are scenario theory's, not formalized here.

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal
      Prediction: Zonotope-Based Uncertainty Quantification for Regression and
      Classification Tasks". Journal of Machine Learning Research, 26(294):1-37, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ι : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.2]: `{α | ∃ β ∈ C, |β| ≤ α}` is convex for convex `C`. -/
theorem Conform.convex_fitsUnder {C : Set (ι → ℝ)} (hC : Convex ℝ C) :
    Convex ℝ {α | Conform.FitsUnder C α} := by -- --- PROOF ---
  rintro α ⟨β, hβC, hβ⟩ α' ⟨β', hβ'C, hβ'⟩ a b ha hb hab
  refine ⟨a • β + b • β', hC hβC hβ'C ha hb hab, fun j => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * β j + b * β' j| ≤ |a * β j| + |b * β' j| := abs_add_le _ _
    _ = a * |β j| + b * |β' j| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * α j + b * α' j :=
        add_le_add (mul_le_mul_of_nonneg_left (hβ j) ha) (mul_le_mul_of_nonneg_left (hβ' j) hb)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
