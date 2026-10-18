module

public import CORALean.ContDynamics.Conform.Theorems.NotIsBoundaryPointIff
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Lattice

@[expose] public section

/-!
# Boundary points from one linear program

[1, Prop. 8]: with `α*` an optimum of (19) or (20), the linear program (23) maximizes `∑ₘ δₘ`
subject to `δₘ ≥ 0`, `-α* ≤ ±βₘ - f δₘ` (`fⱼ = 1` where `α*ⱼ > 0`, else `0`) and each point's
containment constraint; at an optimal solution, point `m` is a boundary point iff `δₘ = 0`.
Each point's constraint is a convex set `Cₘ` of `βₘ`, and `α*` admits every point. Stated for
any optimal solution of (23); when `α* = 0` every `δₘ` is unconstrained above and (23) has
none, which the proposition passes over. The blocks `(βₘ, δₘ)` are independent, so an optimum
has each `δₘ` at its largest, and that is positive iff (24) holds (`not_isBoundaryPoint_iff`).

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

/-- [1, Prop. 8]: at an optimal solution of (23), point `m` is a boundary point iff
`δₘ = 0`. -/
theorem Conform.isBoundaryPoint_iff_lp23 [Fintype ι] [DecidableEq ι] {M : Type} [Fintype M]
    [DecidableEq M] (C : M → Set (ι → ℝ)) (hC : ∀ m, Convex ℝ (C m)) (α : ι → ℝ)
    (hfit : ∀ m, Conform.FitsUnder (C m) α) (β : M → ι → ℝ) (δ : M → ℝ) : -- --- STMT ---
    let fv : ι → ℝ := fun j => if 0 < α j then 1 else 0
    let Feas : M → (ι → ℝ) → ℝ → Prop := fun m b d =>
      0 ≤ d ∧ b ∈ C m ∧ ∀ j, -α j ≤ b j - fv j * d ∧ -α j ≤ -b j - fv j * d
    (∀ m, Feas m (β m) (δ m)) →
    (∀ (β' : M → ι → ℝ) (δ' : M → ℝ), (∀ m, Feas m (β' m) (δ' m)) → ∑ m, δ' m ≤ ∑ m, δ m) →
    ∀ m, Conform.IsBoundaryPoint (C m) α ↔ δ m = 0 := by -- --- PROOF ---
  intro fv Feas hfe hopt m
  have hfv : ∀ j, 0 ≤ fv j := fun j => by simp only [fv]; split_ifs <;> norm_num
  constructor
  · -- at a boundary point a positive `δₘ` would let its `αⱼ` shrink by `δₘ`
    rintro ⟨j, hj, hjb⟩
    obtain ⟨hδ0, hβC, hcon⟩ := hfe m
    by_contra hδ
    have hδpos : 0 < δ m := lt_of_le_of_ne hδ0 (Ne.symm hδ)
    have hfj : fv j = 1 := by simp only [fv, if_pos hj]
    have hcj := hcon j
    rw [hfj, one_mul] at hcj
    refine hjb (δ m) hδpos (by linarith [hcj.1, hcj.2]) ⟨β m, hβC, fun k => ?_⟩
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      exact abs_le.mpr ⟨by linarith [hcj.1], by linarith [hcj.2]⟩
    · rw [Function.update_of_ne hk]
      have hck := hcon k
      have := mul_nonneg (hfv k) hδ0
      exact abs_le.mpr ⟨by linarith [hck.1], by linarith [hck.2]⟩
  · -- otherwise (24) gives a strictly fitting `β'`, and a positive `δ'` for block `m`
    intro hδ
    by_contra hnb
    obtain ⟨β', hβ'C, hβ', hβ's⟩ := (Conform.not_isBoundaryPoint_iff (hC m) (hfit m)).mp hnb
    obtain ⟨δ', hδ'pos, hδ'le⟩ : ∃ δ' > 0, ∀ j, 0 < α j → δ' ≤ α j - |β' j| := by
      rcases isEmpty_or_nonempty ι with hι | hι
      · exact ⟨1, one_pos, fun j => isEmptyElim j⟩
      let g : ι → ℝ := fun j => if 0 < α j then α j - |β' j| else 1
      refine ⟨Finset.univ.inf' Finset.univ_nonempty g,
        (Finset.lt_inf'_iff _).mpr fun j _ => ?_, fun j hj => ?_⟩
      · simp only [g]
        split_ifs with hj
        · linarith [hβ's j hj]
        · exact one_pos
      · have := Finset.inf'_le g (Finset.mem_univ j)
        simp only [g, if_pos hj] at this
        exact this
    -- `(β', δ')` is feasible for block `m`
    have hF : Feas m β' δ' := by
      refine ⟨hδ'pos.le, hβ'C, fun j => ?_⟩
      by_cases hj : 0 < α j
      · have hfj : fv j = 1 := by simp only [fv, if_pos hj]
        rw [hfj, one_mul]
        have h1 := hδ'le j hj
        constructor <;> linarith [neg_abs_le (β' j), le_abs_self (β' j)]
      · have hfj : fv j = 0 := by simp only [fv, if_neg hj]
        rw [hfj, zero_mul, sub_zero, sub_zero]
        exact ⟨by linarith [(abs_le.mp (hβ' j)).1], by linarith [(abs_le.mp (hβ' j)).2]⟩
    -- swapping block `m` raises `∑ δ`, against optimality
    have hsw := hopt (Function.update β m β') (Function.update δ m δ') fun m' => by
      by_cases hm : m' = m
      · subst hm; simp only [Function.update_self]; exact hF
      · simp only [Function.update_of_ne hm]; exact hfe m'
    rw [Finset.sum_update_of_mem (Finset.mem_univ m), ← Finset.sum_erase_add _ _
      (Finset.mem_univ m), hδ, add_zero, Finset.sdiff_singleton_eq_erase] at hsw
    linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
