import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalW
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpWApply
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.QuadTermBetween
import CORALean.ContSet.Interval.Real.Theorems.MemMat
import CORALean.ContSet.Interval.Real.Theorems.MulBetweenCorners
import Mathlib.Tactic.Positivity

/-!
# `W(t)` of every member of an interval matrix lies in `expIntervalW`

[1, Lemma 3.1], the enclosure half. Once `expW_apply` has split the entry into
three pieces each piece is bounded by one fact: `mul_between_corners` for the
single-use product and for every term of the `k ≠ i, j` sum, and
`quadTerm_between` for the diagonal parabola.

Nothing here needs `t ≠ 0` or a non-empty box; both are hypotheses of the
tightness theorem instead, which is the one that would fail without them.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every member's second-order term sits in the interval matrix [1] computes. -/
theorem MatExp.expW_mem_expIntervalW (A : Interval (Mat ℝ n n)) (t : ℝ)
    {M : Mat ℝ n n} (hM : M ∈ A.construct) :
    MatExp.expW M t ∈ (MatExp.expIntervalW A t).construct := by -- --- PROOF ---
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have hm := Interval.mem_mat_iff.mp hM
  have ht2 : (0:ℝ) ≤ t ^ 2 / 2 := by positivity
  -- the `k ≠ i, j` sum, bounded term by term by the four corner products
  have hSlo : ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)),
        Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j)
      ≤ ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), M i k * M k j :=
    Finset.sum_le_sum fun k _ =>
      (Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k j).1 (hm k j).2).1
  have hShi : ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), M i k * M k j
      ≤ ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)),
        Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j) :=
    Finset.sum_le_sum fun k _ =>
      (Interval.mul_between_corners (hm i k).1 (hm i k).2 (hm k j).1 (hm k j).2).2
  -- the leading summand: a single-use product off the diagonal, the parabola on it
  have hfirst : (if i = j then MatExp.quadTermLo t (A.inf i i) (A.sup i i)
        else Interval.mulLo (A.inf i j) (A.sup i j)
          (t + t ^ 2 / 2 * (A.inf i i + A.inf j j)) (t + t ^ 2 / 2 * (A.sup i i + A.sup j j)))
      ≤ (if i = j then MatExp.quadTerm t (M i i)
        else M i j * (t + t ^ 2 / 2 * (M i i + M j j)))
      ∧ (if i = j then MatExp.quadTerm t (M i i)
        else M i j * (t + t ^ 2 / 2 * (M i i + M j j)))
        ≤ (if i = j then MatExp.quadTermHi t (A.inf i i) (A.sup i i)
          else Interval.mulHi (A.inf i j) (A.sup i j)
            (t + t ^ 2 / 2 * (A.inf i i + A.inf j j))
            (t + t ^ 2 / 2 * (A.sup i i + A.sup j j))) := by
    by_cases h : i = j
    · subst h
      simp only [reduceIte]
      exact MatExp.quadTerm_between (hm i i).1 (hm i i).2
    · simp only [if_neg h]
      -- the second factor moves inside its own bounds because `t ² / 2 ≥ 0`
      exact Interval.mul_between_corners (hm i j).1 (hm i j).2
        (by nlinarith [(hm i i).1, (hm j j).1]) (by nlinarith [(hm i i).2, (hm j j).2])
  rw [MatExp.expW_apply]
  simp only [MatExp.expIntervalW]
  exact ⟨add_le_add hfirst.1 (mul_le_mul_of_nonneg_left hSlo ht2),
    add_le_add hfirst.2 (mul_le_mul_of_nonneg_left hShi ht2)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
