import CORALean.ContDynamics.Conform.Theorems.MemZcpSetIff
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Zono-conformal regression with outliers is a mixed-integer program

[1, Prop. 9]: (19e) replaced by `0 = D̄(x⁽ᵐ⁾) G_u βₘ - y_Δ⁽ᵐ⁾ ρₘ` (25a), `n_m - n_out ≤ 1ᵀρ`
(25b), `ρ ∈ {0, 1}ⁿᵐ` (25c): for `α ≥ 0`, the constraints have a solution iff at least
`n_m - n_out` of the data points lie in their prediction sets, at most `n_out` violating
(10b). The points kept are those with `ρₘ = 1`; a discarded point takes `βₘ = 0`.

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

/-- [1, Prop. 9]: (19c), (19d), (25) are feasible iff all but at most `n_out` points meet (10b). -/
theorem Conform.zcp_regression_milp {nm nout : ℕ} (f : Fin nm → Vec ℝ ny)
    (D : Fin nm → Mat ℝ ny nu) (y : Fin nm → Vec ℝ ny) (Gu : ι → Vec ℝ nu) (α : ι → ℝ)
    (hα : ∀ j, 0 ≤ α j) :
    (∃ (β : Fin nm → ι → ℝ) (ρ : Fin nm → ℝ), (∀ m j, 0 ≤ α j + β m j ∧ 0 ≤ α j - β m j) ∧
        (∀ m, (0 : Vec ℝ ny) = ∑ j, β m j • D m *ᵥ Gu j - ρ m • (y m - f m)) ∧
        (nm : ℝ) - nout ≤ ∑ m, ρ m ∧ ∀ m, ρ m = 0 ∨ ρ m = 1) ↔
      ∃ T : Finset (Fin nm), (nm : ℝ) - nout ≤ T.card ∧
        ∀ m ∈ T, y m ∈ Conform.zcpSet (f m) (D m) Gu α := by -- --- PROOF ---
  constructor
  · -- keep the points with `ρₘ = 1`
    rintro ⟨β, ρ, hβ, h25a, h25b, h25c⟩
    have hsum : ∑ m, ρ m = ((Finset.univ.filter fun m => ρ m = 1).card : ℝ) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rcases h25c m with h | h <;> simp [h]
    refine ⟨Finset.univ.filter fun m => ρ m = 1, hsum ▸ h25b, fun m hm => ?_⟩
    have hρ : ρ m = 1 := (Finset.mem_filter.mp hm).2
    refine (Conform.mem_zcpSet_iff _ _ _ _ hα _).mpr ⟨β m, fun j => abs_le.mpr
      ⟨by linarith [(hβ m j).1], by linarith [(hβ m j).2]⟩, ?_⟩
    have h := h25a m
    rw [hρ, one_smul] at h
    rw [eq_sub_iff_add_eq, zero_add] at h
    rw [← h]
    abel
  · -- `ρ` the indicator of the kept points, `β` from (18) on them and `0` elsewhere
    rintro ⟨T, hT, hmem⟩
    have hch : ∀ m, ∃ b : ι → ℝ, m ∈ T →
        (∀ j, |b j| ≤ α j) ∧ y m = f m + ∑ j, b j • D m *ᵥ Gu j := by
      intro m
      by_cases hm : m ∈ T
      · obtain ⟨b, hb, hy⟩ := (Conform.mem_zcpSet_iff _ _ _ _ hα _).mp (hmem m hm)
        exact ⟨b, fun _ => ⟨hb, hy⟩⟩
      · exact ⟨0, fun h => absurd h hm⟩
    choose b hb using hch
    -- (19c), (19d) from `|β| ≤ α`, (25a) from (18) or `0 = 0`, (25b) the count of `T`
    refine ⟨fun m => if m ∈ T then b m else 0, fun m => if m ∈ T then 1 else 0, fun m j => ?_,
      fun m => ?_, ?_, fun m => by by_cases hm : m ∈ T <;> simp [hm]⟩
    · by_cases hm : m ∈ T
      · have := abs_le.mp ((hb m hm).1 j)
        simp only [if_pos hm]
        constructor <;> linarith [this.1, this.2]
      · simp only [if_neg hm, Pi.zero_apply, add_zero, sub_zero]
        exact ⟨hα j, hα j⟩
    · by_cases hm : m ∈ T
      · simp only [if_pos hm, one_smul]
        rw [(hb m hm).2]
        abel
      · simp [hm]
    · rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact hT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
