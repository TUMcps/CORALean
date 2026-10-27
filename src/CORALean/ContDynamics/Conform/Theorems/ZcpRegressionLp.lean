module

public import CORALean.ContDynamics.Conform.Theorems.MemZcpSetIff
public import CORALean.ContDynamics.Conform.Theorems.ZcpIntervalNorm
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Zono-conformal regression is a linear program

[1, Thm. 6]: Problem 1 with the cost (14), over the predictors (13) with `U` from (15), is the
linear program (19). For `α ≥ 0` (19b), some `βₘ` with (19c)-(19e) exists for every data point
iff every `y⁽ᵐ⁾ ∈ Y_ZCP(x⁽ᵐ⁾)` (10b), by [1, Lemma 5]; and the objective (19a) is the cost (10a),
`∑ₘ ∑ᵢ ‖Rᵢ Y_ZCP(x_eval⁽ᵐ⁾)‖_I`, by [1, Lemma 4]. So the program's feasible `α` are exactly the
predictors meeting (10b), at their cost: its optimum is Problem 1's over that class. Data
points and evaluation inputs are any finite families; `R₀ = I` is not used.

## Inputs
* `M` – data point index type
* `E` – evaluation index type
* `nr` – size index of `R`
* `f` – predictions per point
* `D` – derivatives per point
* `y` – targets per point
* `Gu` – uncertainty generators
* `R` – cost rotation matrices
* `Deval` – evaluation derivatives
* `α` – generator scaling

## Hypotheses
* `hα` – scalings nonnegative

## Conclusion
* the regression constraints are those of the linear program and the cost is linear in `α`

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

open Matrix

variable {ny nu : ℕ} {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 6]: (19c)-(19e) are (10b), and (19a) is (10a) with the cost (14). -/
theorem Conform.zcp_regression_lp {M E : Type} [Fintype E] {nr : ℕ}
    (f : M → Vec ℝ ny) (D : M → Mat ℝ ny nu) (y : M → Vec ℝ ny) (Gu : ι → Vec ℝ nu)
    (R : Fin (nr + 1) → Mat ℝ ny ny) (Deval : E → Mat ℝ ny nu) (α : ι → ℝ)
    (hα : ∀ j, 0 ≤ α j) : -- --- CONCL ---
    ((∀ m, ∃ β : ι → ℝ, (∀ j, 0 ≤ α j + β j) ∧ (∀ j, 0 ≤ α j - β j) ∧
        y m - f m = ∑ j, β j • D m *ᵥ Gu j) ↔
      ∀ m, y m ∈ Conform.zcpSet (f m) (D m) Gu α) ∧
    ∑ e, ∑ i, Conform.intervalNorm (fun _ => 1) (fun j => α j • (R i * Deval e) *ᵥ Gu j)
      = ∑ e, ∑ i, ∑ j, (∑ a, |((R i * Deval e) *ᵥ Gu j) a|) * α j := by -- --- PROOF ---
  refine ⟨forall_congr' fun m => ?_, ?_⟩
  · -- (19c), (19d) are `|β| ≤ α`, (19e) the equation of (18)
    rw [Conform.mem_zcpSet_iff _ _ _ _ hα]
    refine exists_congr fun β => ?_
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      refine ⟨fun j => abs_le.mpr ⟨?_, ?_⟩, ?_⟩
      · linarith [h₁ j]
      · linarith [h₂ j]
      · rw [← h₃]; abel
    · rintro ⟨h, h₃⟩
      refine ⟨fun j => ?_, fun j => ?_, ?_⟩
      · linarith [(abs_le.mp (h j)).1]
      · linarith [(abs_le.mp (h j)).2]
      · rw [h₃]; abel
  · -- term by term, [1, Lemma 4]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
    exact (Conform.intervalNorm_zcpSet (R i) 0 (Deval e) Gu α hα).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
