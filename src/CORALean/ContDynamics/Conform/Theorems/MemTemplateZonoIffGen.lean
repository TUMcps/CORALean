module

public import CORALean.ContDynamics.Conform.Definitions.TemplateZono
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# A stretched template, by its scaled coefficients

`y ∈ ⟨c, G diag(α)⟩` for `α ≥ 0` iff `y = c + ∑ⱼ βⱼ gⱼ` for some `|β| ≤ α`: the substitution
`β = diag(α) λ` behind the generator constraints of [1, Lemma 4] and [2, Lemma 5], linear in
`α` and `β` together. Where `αⱼ = 0`, `βⱼ = 0` is forced and the generator drops out.

## References

* [1] L. Lützow and M. Althoff. "Reachset-Conformant System Identification". IEEE
      Transactions on Automatic Control, 71(5):3014-3029, 2026.
* [2] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal
      Prediction: Zonotope-Based Uncertainty Quantification for Regression and
      Classification Tasks". Journal of Machine Learning Research, 26(294):1-37, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 4], [2, Lemma 5]: membership in `⟨c, G diag(α)⟩`, `α ≥ 0`, with `βⱼ = αⱼ λⱼ`
in place of `λⱼ`. -/
theorem Conform.mem_templateZono_iff_gen {m : ℕ} {ι : Type} [Fintype ι] (c : Vec ℝ m)
    (G : ι → Vec ℝ m) (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) (y : Vec ℝ m) :
    y ∈ Conform.templateZono c G α ↔
      ∃ β : ι → ℝ, (∀ j, |β j| ≤ α j) ∧ y = c + ∑ j, β j • G j := by -- --- PROOF ---
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun j => l j * α j, fun j => ?_, by simp only [smul_smul]⟩
    rw [abs_mul, abs_of_nonneg (hα j)]
    exact mul_le_of_le_one_left (hα j) (hl j)
  · rintro ⟨β, hβ, rfl⟩
    -- `λⱼ = βⱼ / αⱼ`, and `0` where `αⱼ = 0` (then `βⱼ = 0` too)
    refine ⟨fun j => β j / α j, fun j => ?_, ?_⟩
    · rcases (hα j).lt_or_eq with hpos | hzero
      · rw [abs_div, abs_of_pos hpos, div_le_one hpos]
        exact hβ j
      · simp [← hzero]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      show β j = β j / α j * α j
      rcases (hα j).lt_or_eq with hpos | hzero
      · field_simp
      · have : β j = 0 := abs_nonpos_iff.mp (hzero ▸ hβ j)
        simp [this, ← hzero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
