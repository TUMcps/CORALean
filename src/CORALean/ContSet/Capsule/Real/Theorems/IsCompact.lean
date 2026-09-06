import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqEmpty
import CORALean.ContSet.Capsule.Real.Theorems.ConstructEqAdd

/-!
# A capsule is compact

At `C.r < 0` the set is `∅`. Otherwise `construct_eq_add` writes `C.construct`
as the sum of the segment, a continuous image of the compact `Icc`, and the
ball, closed (the sum of squares is continuous) and bounded (no coordinate of
a point inside it exceeds `C.r` in size) in the finite-dimensional `Vec ℝ n`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.isCompact_construct (C : Capsule n) : IsCompact C.construct := by -- --- PROOF ---
  rcases lt_or_ge C.r 0 with hr | hr
  · rw [Capsule.construct_eq_empty hr]
    exact isCompact_empty
  · have hball : IsCompact {y : Vec ℝ n | ∑ i, y i ^ 2 ≤ C.r ^ 2} := by
      refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec ℝ n) C.r)
        (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)
          continuous_const) fun y hy => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr]
      intro i
      rw [Real.norm_eq_abs]
      refine abs_le_of_sq_le_sq ?_ hr
      calc y i ^ 2 ≤ ∑ j, y j ^ 2 :=
            Finset.single_le_sum (f := fun j => y j ^ 2) (fun _ _ => sq_nonneg _)
              (Finset.mem_univ i)
        _ ≤ C.r ^ 2 := hy
    have hseg : IsCompact ((fun t : ℝ => C.c + t • C.g) '' Set.Icc (-1 : ℝ) 1) :=
      isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
    rw [Capsule.construct_eq_add hr]
    exact hseg.add hball

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
