module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The image of a box under a nonnegative matrix need not be a box

[1, Lemma 5] prints `Box(A I) = A I = [A a, A b]` for `A ≥ 0`. The second equality is false:
`A = [1 1; 1 1]` maps `[0, 1]²` onto the diagonal segment from `0` to `(2, 2)`, which misses
`(2, 0) ∈ [A a, A b] = [0, 2]²`. The hull equality holds (`hull_image_of_nonneg`), and is all
the proof of [1, Thm. 7] needs.

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.image_of_nonneg_counterexample : -- --- CONCL ---
    let A : Mat ℝ 2 2 := fun _ _ => 1
    let a : Vec ℝ 2 := fun _ => 0
    let b : Vec ℝ 2 := fun _ => 1
    (∀ i j, 0 ≤ A i j) ∧ (∀ j, a j ≤ b j) ∧
      (A *ᵥ ·) '' (⟨a, b⟩ : Interval (Vec ℝ 2)).construct ≠
        (⟨A *ᵥ a, A *ᵥ b⟩ : Interval (Vec ℝ 2)).construct := by -- --- PROOF ---
  intro A a b
  refine ⟨fun _ _ => zero_le_one, fun _ => zero_le_one, fun h => ?_⟩
  -- `(2, 0)` is in the box `[0, 2]²`
  have hmem : (![2, 0] : Vec ℝ 2) ∈ (⟨A *ᵥ a, A *ᵥ b⟩ : Interval (Vec ℝ 2)).construct := by
    intro i
    change (A *ᵥ a) i ≤ (![2, 0] : Vec ℝ 2) i ∧ (![2, 0] : Vec ℝ 2) i ≤ (A *ᵥ b) i
    fin_cases i <;> simp [A, a, b, mulVec, dotProduct]
  rw [← h] at hmem
  obtain ⟨x, -, hx⟩ := hmem
  -- but both coordinates of `A x` are `x₀ + x₁`
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp [A, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
