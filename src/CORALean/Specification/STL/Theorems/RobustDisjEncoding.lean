module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-!
# The robust disjunction constraints compute the maximum

[1, Sec. V (disjunction)]: conjunction's encoding with (4) replaced by `r ≥ rᵢ` enforces
`r = maxᵢ rᵢ`: the one `pⱼ = 1` pins `r ≤ rⱼ`. Feasible for `M` at least the spread of the `rᵢ`.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.robust_disj_encoding {m : ℕ} (hm : 0 < m) (rs : Fin m → ℝ) (M : ℝ) : -- --- STMT ---
    let H : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (∀ (r : ℝ) (p : Fin m → ℝ), (∀ i, p i = 0 ∨ p i = 1) → ∑ i, p i = 1 →
      (∀ i, rs i ≤ r) → (∀ i, rs i - (1 - p i) * M ≤ r ∧ r ≤ rs i + M * (1 - p i)) →
      r = Finset.univ.sup' H rs) ∧
    ((∀ i j, rs i - rs j ≤ M) → ∃ p : Fin m → ℝ, (∀ i, p i = 0 ∨ p i = 1) ∧ ∑ i, p i = 1 ∧
      (∀ i, rs i ≤ Finset.univ.sup' H rs) ∧ ∀ i, rs i - (1 - p i) * M ≤ Finset.univ.sup' H rs ∧
        Finset.univ.sup' H rs ≤ rs i + M * (1 - p i)) := by -- --- PROOF ---
  intro H
  refine ⟨fun r p hp hsum h4 h5 => ?_, fun hM => ?_⟩
  · -- some `pⱼ` is `1`, else the sum is `0`
    obtain ⟨j, hj⟩ : ∃ j, p j = 1 := by
      by_contra hno
      simp only [not_exists] at hno
      have : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => (hp i).resolve_right (hno i)
      linarith
    have hrj : r ≤ rs j := by have := (h5 j).2; rw [hj] at this; linarith
    exact le_antisymm (hrj.trans (Finset.le_sup' _ (Finset.mem_univ j)))
      (Finset.sup'_le H _ fun i _ => h4 i)
  · -- select the maximizer
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ rs H
    have hmax : Finset.univ.sup' H rs = rs j :=
      le_antisymm (Finset.sup'_le H _ fun i hi => hj i hi) (Finset.le_sup' _ (Finset.mem_univ j))
    have hM0 : 0 ≤ M := by have := hM j j; linarith
    refine ⟨fun i => if i = j then 1 else 0, fun i => by by_cases h : i = j <;> simp [h],
      by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true],
      fun i => Finset.le_sup' _ (Finset.mem_univ i), fun i => ?_⟩
    rw [hmax]
    by_cases h : i = j
    · subst h; simp
    · simp only [h, if_false, sub_zero, one_mul, mul_one]
      exact ⟨by linarith [hj i (Finset.mem_univ i)], by linarith [hM j i]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
