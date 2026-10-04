import CORALean.ContDynamics.Conform.Theorems.ClassesVecSingleSubsetIff
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Zono-conformal classification with outliers is a mixed-integer program

[1, Prop. 10]: (20e) replaced by `0 ≤ Tₘ D̄(x⁽ᵐ⁾) G_u βₘ + Tₘ f(x⁽ᵐ⁾) ρₘ` (26a),
`n_m - n_out ≤ 1ᵀρ` (26b), `ρ ∈ {0, 1}ⁿᵐ` (26c): for `α ≥ 0` and one-hot outputs, the
constraints have a solution iff at least `n_m - n_out` points meet (12b). At `ρₘ = 0`, `βₘ = 0`
satisfies (26a) trivially, as the paper's proof by analogy with [1, Prop. 9] says.

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal
      Prediction: Zonotope-Based Uncertainty Quantification for Regression and
      Classification Tasks". Journal of Machine Learning Research, 26(294):1-37, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {ny nu : ℕ} {ι : Type} [Fintype ι]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 10]: (20c), (20d), (26) are feasible iff all but at most `n_out` points meet
(12b). -/
theorem Conform.zcp_classification_milp {nm nout : ℕ} (f : Fin nm → Vec ℝ ny)
    (D : Fin nm → Mat ℝ ny nu) (c : Fin nm → Fin ny) (Gu : ι → Vec ℝ nu) (α : ι → ℝ)
    (hα : ∀ j, 0 ≤ α j) :
    (∃ (β : Fin nm → ι → ℝ) (ρ : Fin nm → ℝ), (∀ m j, 0 ≤ α j + β m j ∧ 0 ≤ α j - β m j) ∧
        (∀ m, 0 ≤ Conform.classMat (c m) *ᵥ (∑ j, β m j • D m *ᵥ Gu j)
          + ρ m • (Conform.classMat (c m) *ᵥ f m)) ∧
        (nm : ℝ) - nout ≤ ∑ m, ρ m ∧ ∀ m, ρ m = 0 ∨ ρ m = 1) ↔
      ∃ T : Finset (Fin nm), (nm : ℝ) - nout ≤ T.card ∧
        ∀ m ∈ T, Conform.classesVec (Pi.single (c m) 1 : Vec ℝ ny)
          ⊆ Conform.classesSet (Conform.zcpSet (f m) (D m) Gu α) := by -- --- PROOF ---
  -- at `ρₘ = 1`, (26a) is (20e)
  have h26 : ∀ m (b : ι → ℝ), (0 ≤ Conform.classMat (c m) *ᵥ (∑ j, b j • D m *ᵥ Gu j)
      + (1 : ℝ) • (Conform.classMat (c m) *ᵥ f m)) ↔
      -(Conform.classMat (c m) *ᵥ f m) ≤ Conform.classMat (c m) *ᵥ ∑ j, b j • D m *ᵥ Gu j := by
    intro m b
    rw [one_smul]
    constructor
    · intro h i; have := h i; simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at this ⊢
      linarith
    · intro h i; have := h i; simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at this ⊢
      linarith
  constructor
  · -- keep the points with `ρₘ = 1`
    rintro ⟨β, ρ, hβ, h26a, h26b, h26c⟩
    have hsum : ∑ m, ρ m = ((Finset.univ.filter fun m => ρ m = 1).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rcases h26c m with h | h <;> simp [h]
    refine ⟨Finset.univ.filter fun m => ρ m = 1, hsum ▸ h26b, fun m hm => ?_⟩
    have hρ : ρ m = 1 := (Finset.mem_filter.mp hm).2
    have h := h26a m
    rw [hρ, h26] at h
    exact (Conform.classesVec_single_subset_iff _ _ _ _ _ hα).mpr ⟨β m, fun j => abs_le.mpr
      ⟨by linarith [(hβ m j).1], by linarith [(hβ m j).2]⟩, h⟩
  · -- `ρ` the indicator of the kept points, `β` from (20e) on them and `0` elsewhere
    rintro ⟨T, hT, hmem⟩
    have hch : ∀ m, ∃ b : ι → ℝ, m ∈ T → (∀ j, |b j| ≤ α j) ∧
        -(Conform.classMat (c m) *ᵥ f m) ≤ Conform.classMat (c m) *ᵥ ∑ j, b j • D m *ᵥ Gu j := by
      intro m
      by_cases hm : m ∈ T
      · obtain ⟨b, hb, h⟩ := (Conform.classesVec_single_subset_iff _ _ _ _ _ hα).mp (hmem m hm)
        exact ⟨b, fun _ => ⟨hb, h⟩⟩
      · exact ⟨0, fun h => absurd h hm⟩
    choose b hb using hch
    -- (20c), (20d) from `|β| ≤ α`, (26a) from (20e) or `0 ≤ 0`, (26b) the count of `T`
    refine ⟨fun m => if m ∈ T then b m else 0, fun m => if m ∈ T then 1 else 0, fun m j => ?_,
      fun m => ?_, ?_, fun m => by by_cases hm : m ∈ T <;> simp [hm]⟩
    · by_cases hm : m ∈ T
      · have := abs_le.mp ((hb m hm).1 j)
        simp only [if_pos hm]
        constructor <;> linarith [this.1, this.2]
      · simp only [if_neg hm, Pi.zero_apply, add_zero, sub_zero]
        exact ⟨hα j, hα j⟩
    · by_cases hm : m ∈ T
      · simp only [if_pos hm]
        exact (h26 m (b m)).mpr (hb m hm).2
      · simp [hm]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact hT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
