module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-!
# The robust conjunction constraints compute the minimum

[1, Eq. 3-5]: with binaries `pᵢ`, `Σᵢ pᵢ = 1` (3), `r ≤ rᵢ` (4) and
`rᵢ - (1 - pᵢ)M ≤ r ≤ rᵢ + M(1 - pᵢ)` (5) enforce `r = minᵢ rᵢ`: the one `pⱼ = 1` pins `r ≥ rⱼ`,
and (4) does the rest, whatever `M`. The minimum is feasible for `M` at least the spread of the
`rᵢ`, the "sufficiently large" of the text. [1, Sec. V (disjunction)] is the mirror image.

## Inputs
* `m` – number of operands
* `rs` – operand robustness values
* `M` – big constant

## Hypotheses
* `hm` – there is an operand

## Conclusion
* the constraints force the minimum and it exists

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

theorem STL.robust_conj_encoding {m : ℕ} (hm : 0 < m) (rs : Fin m → ℝ) (M : ℝ) : -- --- CONCL ---
    let H : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (∀ (r : ℝ) (p : Fin m → ℝ), (∀ i, p i = 0 ∨ p i = 1) → ∑ i, p i = 1 →
      (∀ i, r ≤ rs i) → (∀ i, rs i - (1 - p i) * M ≤ r ∧ r ≤ rs i + M * (1 - p i)) →
      r = Finset.univ.inf' H rs) ∧
    ((∀ i j, rs i - rs j ≤ M) → ∃ p : Fin m → ℝ, (∀ i, p i = 0 ∨ p i = 1) ∧ ∑ i, p i = 1 ∧
      (∀ i, Finset.univ.inf' H rs ≤ rs i) ∧ ∀ i, rs i - (1 - p i) * M ≤ Finset.univ.inf' H rs ∧
        Finset.univ.inf' H rs ≤ rs i + M * (1 - p i)) := by -- --- PROOF ---
  intro H
  refine ⟨fun r p hp hsum h4 h5 => ?_, fun hM => ?_⟩
  · -- some `pⱼ` is `1`, else the sum is `0`
    obtain ⟨j, hj⟩ : ∃ j, p j = 1 := by
      by_contra hno
      simp only [not_exists] at hno
      have : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => (hp i).resolve_right (hno i)
      linarith
    have hrj : rs j ≤ r := by have := (h5 j).1; rw [hj] at this; linarith
    exact le_antisymm (Finset.le_inf' H _ fun i _ => h4 i)
      ((Finset.inf'_le _ (Finset.mem_univ j)).trans hrj)
  · -- select the minimizer
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ rs H
    have hmin : Finset.univ.inf' H rs = rs j :=
      le_antisymm (Finset.inf'_le _ (Finset.mem_univ j)) (Finset.le_inf' H _ fun i hi => hj i hi)
    have hM0 : 0 ≤ M := by have := hM j j; linarith
    refine ⟨fun i => if i = j then 1 else 0, fun i => by by_cases h : i = j <;> simp [h],
      by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true],
      fun i => Finset.inf'_le _ (Finset.mem_univ i), fun i => ?_⟩
    rw [hmin]
    by_cases h : i = j
    · subst h; simp
    · simp only [h, if_false, sub_zero, one_mul, mul_one]
      exact ⟨by linarith [hM i j], by linarith [hj i (Finset.mem_univ i)]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
