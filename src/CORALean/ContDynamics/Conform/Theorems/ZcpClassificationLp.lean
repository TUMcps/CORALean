module

public import CORALean.ContDynamics.Conform.Theorems.ClassesVecSingleSubsetIff
public import CORALean.ContDynamics.Conform.Theorems.ZcpIntervalNorm
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Zono-conformal classification is a linear program

[1, Thm. 7]: Problem 2 with the cost (14), over the predictors (13) with `U` from (15), is the
linear program (20). Each data point carries one class `c⁽ᵐ⁾`, its output the unit vector
`e_c` (22), so `classes(y⁽ᵐ⁾) = {c⁽ᵐ⁾}`; `Tₘ = vert(e_cᵀ) - I` (21) has `(Tₘ z)ᵢ = z_c - zᵢ`. For
`α ≥ 0`, some `βₘ` with (20c)-(20e) exists for every point iff (12b) holds for every point, and
(20a) is the cost (12a), by [1, Lemma 4]. Multi-label data enter as several one-hot points,
as the paper builds them.

## Inputs
* `M` – data point index type
* `E` – evaluation index type
* `nr` – size index of `R`
* `f` – predictions per point
* `D` – derivatives per point
* `c` – class per point
* `Gu` – uncertainty generators
* `R` – cost rotation matrices
* `Deval` – evaluation derivatives
* `α` – generator scaling

## Hypotheses
* `hα` – scalings nonnegative

## Conclusion
* the class constraints are those of the linear program and the cost is linear in `α`

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

/-- [1, Thm. 7]: (20c)-(20e) are (12b) at one-hot outputs, and (20a) is (12a) with the cost
(14). -/
theorem Conform.zcp_classification_lp {M E : Type} [Fintype E] {nr : ℕ}
    (f : M → Vec ℝ ny) (D : M → Mat ℝ ny nu) (c : M → Fin ny) (Gu : ι → Vec ℝ nu)
    (R : Fin (nr + 1) → Mat ℝ ny ny) (Deval : E → Mat ℝ ny nu) (α : ι → ℝ)
    (hα : ∀ j, 0 ≤ α j) : -- --- CONCL ---
    ((∀ m, ∃ β : ι → ℝ, (∀ j, 0 ≤ α j + β j) ∧ (∀ j, 0 ≤ α j - β j) ∧
        -(Conform.classMat (c m) *ᵥ f m) ≤ Conform.classMat (c m) *ᵥ ∑ j, β j • D m *ᵥ Gu j) ↔
      ∀ m, Conform.classesVec (Pi.single (c m) 1 : Vec ℝ ny)
        ⊆ Conform.classesSet (Conform.zcpSet (f m) (D m) Gu α)) ∧
    ∑ e, ∑ i, Conform.intervalNorm (fun _ => 1) (fun j => α j • (R i * Deval e) *ᵥ Gu j)
      = ∑ e, ∑ i, ∑ j, (∑ a, |((R i * Deval e) *ᵥ Gu j) a|) * α j := by -- --- PROOF ---
  refine ⟨forall_congr' fun m => ?_, ?_⟩
  · -- (20c), (20d) are `|β| ≤ α`, and (20e) is (12b) by the proof's chain
    rw [Conform.classesVec_single_subset_iff _ _ _ _ _ hα]
    refine exists_congr fun β => ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨fun j => abs_le.mpr ⟨?_, ?_⟩, h₃⟩,
      fun ⟨h, h₃⟩ => ⟨fun j => ?_, fun j => ?_, h₃⟩⟩
    · linarith [h₁ j]
    · linarith [h₂ j]
    · linarith [(abs_le.mp (h j)).1]
    · linarith [(abs_le.mp (h j)).2]
  · -- term by term, [1, Lemma 4]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => ?_
    exact (Conform.intervalNorm_zcpSet (R i) 0 (Deval e) Gu α hα).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
