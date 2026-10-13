import CORALean.ContDynamics.Conform.Theorems.ZcpSetEq
import CORALean.ContDynamics.Conform.Theorems.MemTemplateZonoIffGen

/-!
# Membership in a prediction set, by coefficients

[1, Lemma 5]: for `α ≥ 0`, `y ∈ Y_ZCP(x)` iff `y = f(x) + D̄(x) G_u β̄` for some `|β̄| ≤ α` (18):
[1, Lemma 3] and the substitution `β̄ = diag(α) λ` (`mem_templateZono_iff_gen`), as in
Lützow and Althoff's `mem_gloSet_iff_gen`.

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

variable {ny nu : ℕ} {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 5]: `y ∈ Y_ZCP(x)` iff `∃ β̄, |β̄| ≤ α, y = f(x) + D̄(x) G_u β̄`. -/
theorem Conform.mem_zcpSet_iff (fx : Vec ℝ ny) (D : Mat ℝ ny nu) (Gu : ι → Vec ℝ nu) (α : ι → ℝ)
    (hα : ∀ j, 0 ≤ α j) (y : Vec ℝ ny) :
    y ∈ Conform.zcpSet fx D Gu α ↔
      ∃ β : ι → ℝ, (∀ j, |β j| ≤ α j) ∧ y = fx + ∑ j, β j • D *ᵥ Gu j := by
  rw [Conform.zcpSet_eq]
  exact Conform.mem_templateZono_iff_gen fx _ α hα y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
