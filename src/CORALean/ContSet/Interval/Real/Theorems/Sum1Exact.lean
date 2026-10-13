module

public import CORALean.ContSet.Interval.Real.Operations.Sum1
public import CORALean.ContSet.Interval.Real.Operations.IsNonempty
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `Interval.sum₁` is exactly the set of column sums

For a nonempty interval matrix the column sums of the matrices in the box fill the summed bounds
entirely: the entries of a column vary independently, so a target between `∑ inf` and `∑ sup` is
reached by moving every entry the same fraction of the way from `inf` to `sup` (`aux_exists_sum`).
Nonemptiness is needed, an empty box having no sums.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_exists_sum {ι : Type} [Fintype ι] {a b : ι → ℝ} (hab : ∀ i, a i ≤ b i) {y : ℝ}
    (h₁ : ∑ i, a i ≤ y) (h₂ : y ≤ ∑ i, b i) :
    ∃ x : ι → ℝ, (∀ i, a i ≤ x i ∧ x i ≤ b i) ∧ ∑ i, x i = y := by -- --- PROOF ---
  have hW : 0 ≤ ∑ i, (b i - a i) := Finset.sum_nonneg fun i _ => sub_nonneg.2 (hab i)
  have hWe : ∑ i, (b i - a i) = ∑ i, b i - ∑ i, a i := by rw [Finset.sum_sub_distrib]
  rcases hW.eq_or_lt with h0 | hpos
  · -- zero total width: the lower bounds already sum to `y`
    refine ⟨a, fun i => ⟨le_refl _, hab i⟩, ?_⟩
    linarith
  · -- move every entry the same fraction `t` of the way from `a` to `b`
    set t := (y - ∑ i, a i) / ∑ i, (b i - a i) with ht
    have ht₀ : 0 ≤ t := div_nonneg (by linarith) hW
    have ht₁ : t ≤ 1 := by
      rw [ht, div_le_one hpos]
      linarith
    refine ⟨fun i => a i + t * (b i - a i), fun i => ⟨?_, ?_⟩, ?_⟩
    · nlinarith [mul_nonneg ht₀ (sub_nonneg.2 (hab i))]
    · nlinarith [mul_nonneg (sub_nonneg.2 ht₁) (sub_nonneg.2 (hab i))]
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ht, div_mul_cancel₀ _ hpos.ne']
      ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sum₁_exact {I : Interval (Mat ℝ m n)} (hI : I.IsNonempty) :
    I.sum₁.construct =
      (fun A : Mat ℝ m n => fun j => ∑ i, A i j) '' I.construct := by -- --- PROOF ---
  ext y
  constructor
  · intro hy
    have key : ∀ j, ∃ x : Fin m → ℝ, (∀ i, I.inf i j ≤ x i ∧ x i ≤ I.sup i j) ∧
        ∑ i, x i = y j := fun j =>
      aux_exists_sum (fun i => hI (i, j)) (hy j).1 (hy j).2
    choose x hx hxy using key
    exact ⟨fun i j => x j i, fun p => hx p.2 p.1, funext hxy⟩
  · rintro ⟨A, hA, rfl⟩ j
    exact ⟨Finset.sum_le_sum (s := Finset.univ) fun i _ => (hA (i, j)).1,
      Finset.sum_le_sum (s := Finset.univ) fun i _ => (hA (i, j)).2⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
