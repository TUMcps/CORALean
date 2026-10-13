module

public import CORALean.NN.Layers.Definitions.Relu
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# ReLU between a line and the line raised by its gap

Above the line of slope `λ` through the origin, and below it raised by `reluGapOfSlope`: the
two ends of the relaxation before recentring. Stated for an arbitrary slope in `[0, 1]`, which is
all convexity gives and all a layer needs, whatever precision it chose its slope in. With
`reluGapOfSlope_eq_ite` naming the gap, these are the two families of parallelograms of
[1, Fig. 1], each sound over its range of slopes.

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem relu_bounds_of_slope {lam l u t : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hl : l ≤ t) (hu : t ≤ u) :
    0 ≤ relu t - lam * t ∧ relu t - lam * t ≤ reluGapOfSlope lam l u := by -- --- PROOF ---
  rcases le_total 0 t with ht | ht
  · have hrt : relu t = t := max_eq_left ht
    refine ⟨by rw [hrt]; nlinarith, ?_⟩
    rw [hrt, reluGapOfSlope]
    exact le_trans (by nlinarith) (le_max_left _ _)
  · have hrt : relu t = 0 := max_eq_right ht
    refine ⟨by rw [hrt]; nlinarith, ?_⟩
    rw [hrt, reluGapOfSlope]
    exact le_trans (by nlinarith) (le_max_right _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
