import CORALean.ContSet.Zonotope.Real.Theorems.AbsBoundLeOfSubsetClosedBall
import CORALean.ContSet.Zonotope.Real.Theorems.SubsetClosedBallOfAbsBoundLe
import CORALean.Specification.STL.Operations.DepBox

/-!
# `interval(·)` does not leave the ball

[1, Prop. 4]: Alg. 1 boxes `C₀` and `D_i` by `interval(·)`, the `n` axis-aligned generators of the
row sums
of `|G|`. The box has the same `absBound` as the zonotope it encloses, so a zonotope inside the sup
norm ball `B_r(0)` has its box inside `B_r(0)` as well (a coordinatewise statement, which the sup
norm respects).

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.depBox_subset_closedBall {Z : Zonotope (Vec ℝ n)} {r : ℝ} (hr : 0 ≤ r)
    (h : Z.construct ⊆ Metric.closedBall (0 : Vec ℝ n) r) :
    (STL.depBox Z).construct ⊆ Metric.closedBall (0 : Vec ℝ n) r := by -- --- PROOF ---
  refine Zonotope.subset_closedBall_of_absBound_le hr fun j => ?_
  refine le_trans (le_of_eq ?_) (Zonotope.absBound_le_of_subset_closedBall h j)
  have hsum : ∑ l : Fin n, |Matrix.diagonal (fun i => ∑ l, |Z.G l i|) l j|
      = ∑ l, |Z.G l j| := by
    rw [Finset.sum_eq_single j, Matrix.diagonal_apply_eq]
    · exact abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ hb, abs_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  show |Z.c j| + ∑ l : Fin n, |Matrix.diagonal (fun i => ∑ l, |Z.G l i|) l j| = _
  rw [hsum]; rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
