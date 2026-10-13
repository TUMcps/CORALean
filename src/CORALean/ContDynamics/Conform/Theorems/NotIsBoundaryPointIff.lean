module

public import CORALean.ContDynamics.Conform.Definitions.ZonoConformal
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A point is not a boundary point iff one `β` fits strictly

The step (24) in the proof of [1, Prop. 8]: at `α ≥ 0` that admits the point, no single
`αⱼ > 0` blocks it iff one `β ∈ C` has `|β| ≤ α` and `|βⱼ| < αⱼ` wherever `αⱼ > 0`. The paper
asserts the equivalence; one direction needs a `β` per coordinate, and `C` convex (an affine
set for (19e), a polyhedron for (20e)) lets their average serve all at once.

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

/-- [1, Prop. 8], (24): not a boundary point iff some `β ∈ C` fits strictly in every `αⱼ > 0`. -/
theorem Conform.not_isBoundaryPoint_iff [Fintype ι] [DecidableEq ι] {C : Set (ι → ℝ)}
    (hC : Convex ℝ C) {α : ι → ℝ} (hfit : Conform.FitsUnder C α) :
    ¬ Conform.IsBoundaryPoint C α ↔
      ∃ β ∈ C, (∀ j, |β j| ≤ α j) ∧ ∀ j, 0 < α j → |β j| < α j := by -- --- PROOF ---
  constructor
  · intro hnb
    obtain ⟨β₀, hβ₀C, hβ₀⟩ := hfit
    -- one `β` per coordinate `j`, strict in `j`
    have hred : ∀ j, ∃ b ∈ C, (∀ k, |b k| ≤ α k) ∧ (0 < α j → |b j| < α j) := by
      intro j
      by_cases hj : 0 < α j
      · simp only [Conform.IsBoundaryPoint, not_exists, not_and, not_forall, not_not] at hnb
        obtain ⟨ε, hε, _, b, hbC, hb⟩ := hnb j hj
        refine ⟨b, hbC, fun k => ?_, fun _ => ?_⟩
        · by_cases hk : k = j
          · subst hk
            have := hb k
            rw [Function.update_self] at this
            linarith
          · have := hb k
            rwa [Function.update_of_ne hk] at this
        · have := hb j
          rw [Function.update_self] at this
          linarith
      · exact ⟨β₀, hβ₀C, hβ₀, fun h => absurd h hj⟩
    choose b hbC hb hbs using hred
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨β₀, hβ₀C, hβ₀, fun j => isEmptyElim j⟩
    -- their average, a convex combination, is strict in every coordinate at once
    have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
    have hval : ∀ k, (∑ j, (1 / (Fintype.card ι : ℝ)) • b j) k
        = ∑ j, (1 / (Fintype.card ι : ℝ)) * b j k := fun k => by
      rw [Finset.sum_apply]; rfl
    have hsum : ∀ k, ∑ _j : ι, (1 / (Fintype.card ι : ℝ)) * α k = α k := fun k => by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
    refine ⟨∑ j, (1 / (Fintype.card ι : ℝ)) • b j,
      hC.sum_mem (fun _ _ => by positivity) (by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
        (fun j _ => hbC j), fun k => ?_, fun k hk => ?_⟩
    · -- within `α`, as every `b j` is
      rw [hval]
      calc |∑ j, 1 / (Fintype.card ι : ℝ) * b j k|
          ≤ ∑ j, |1 / (Fintype.card ι : ℝ) * b j k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : ι, 1 / (Fintype.card ι : ℝ) * α k := Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_pos (by positivity)]
            exact mul_le_mul_of_nonneg_left (hb j k) (by positivity)
        _ = α k := hsum k
    · -- strict in `k`, as `b k` is
      rw [hval]
      calc |∑ j, 1 / (Fintype.card ι : ℝ) * b j k|
          ≤ ∑ j, |1 / (Fintype.card ι : ℝ) * b j k| := Finset.abs_sum_le_sum_abs _ _
        _ < ∑ _j : ι, 1 / (Fintype.card ι : ℝ) * α k := by
            refine Finset.sum_lt_sum (fun j _ => ?_) ⟨k, Finset.mem_univ k, ?_⟩
            · rw [abs_mul, abs_of_pos (by positivity)]
              exact mul_le_mul_of_nonneg_left (hb j k) (by positivity)
            · rw [abs_mul, abs_of_pos (by positivity)]
              exact mul_lt_mul_of_pos_left (hbs k hk) (by positivity)
        _ = α k := hsum k
  · -- reducing `αⱼ` by its slack `αⱼ - |βⱼ|` keeps `β`
    rintro ⟨β, hβC, hβ, hβs⟩ ⟨j, hj, hjb⟩
    refine hjb (α j - |β j|) (by linarith [hβs j hj]) (by linarith [abs_nonneg (β j)])
      ⟨β, hβC, fun k => ?_⟩
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      linarith
    · rw [Function.update_of_ne hk]
      exact hβ k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
