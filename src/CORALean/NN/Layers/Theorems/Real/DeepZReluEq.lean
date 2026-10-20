module

public import CORALean.NN.Layers.Definitions.DeepZRelu
public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Operations.ReluSlope

@[expose] public section

/-!
# DeepZ's ReLU transformer is the tree's ReLU relaxation at its default slope

At ℝ, on every box `l ≤ u`, [1, Thm. 3.1]'s Eq. (5) and `reluRelaxation reluSlope` agree in
slope, offset and error: both are exact on a stable neuron and take the secant `u / (u - l)`
on a crossing one, where ReLU's gap above the secant is the same at both ends, `-u l / (u - l)`,
and recentering halves it into DeepZ's `μ`. At `l = 0 < u` the two take different branches to
the same values. So the soundness of the tree's relaxation, stated once for every scalar, is
DeepZ's at ℝ and its float counterpart elsewhere.

## Inputs
* `l` – lower end of the box
* `u` – upper end of the box

## Hypotheses
* `hlu` – box is ordered

## Conclusion
* DeepZ's slope, offset and error equal the ReLU relaxation's

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem deepZRelu_eq_reluRelaxation {l u : ℝ} (hlu : l ≤ u) : -- --- CONCL ---
    deepZRelu.slope l u = (reluRelaxation reluSlope).slope l u
      ∧ deepZRelu.offset l u = (reluRelaxation reluSlope).offset l u
      ∧ deepZRelu.error l u = (reluRelaxation reluSlope).error l u := by -- --- PROOF ---
  -- the tree's side at ℝ: every rounding exact, `le` the order
  have hs : (reluRelaxation reluSlope).slope l u = max 0 (min 1
      (if u ≤ 0 then 0 else if 0 ≤ l then 1 else u / (u + -l))) := by
    show max 0 (min 1 (if decide (u ≤ 0) = true then (0:ℝ)
      else if decide (0 ≤ l) = true then 1 else u / (u + -l))) = _
    simp only [decide_eq_true_eq]
  have hg : ∀ lam : ℝ, reluGapUp lam l u = max (u + -(lam * u)) (-(lam * l)) := fun _ => rfl
  have ho : (reluRelaxation reluSlope).offset l u
      = reluGapUp ((reluRelaxation reluSlope).slope l u) l u / 2 := rfl
  have he : (reluRelaxation reluSlope).error l u
      = reluGapUp ((reluRelaxation reluSlope).slope l u) l u / 2 := rfl
  rw [ho, he, hg, hs]
  simp only [deepZRelu]
  by_cases hu : u ≤ 0
  · -- stable at zero: slope `0`, and no gap
    have hl : ¬ 0 < l := fun h => absurd (lt_of_lt_of_le h hlu) (not_lt.mpr hu)
    simp [hl, hu]
  · push Not at hu
    by_cases hl0 : 0 ≤ l
    · -- stable at the identity: slope `1`, and no gap
      rcases eq_or_lt_of_le hl0 with h | h
      · subst h; simp [not_le.mpr hu, div_self (ne_of_gt hu)]
      · simp [h, not_le.mpr hu, hl0]
    · -- crossing: the secant, whose gap is the same at both ends
      push Not at hl0
      have hne : u - l ≠ 0 := by linarith
      rw [← sub_eq_add_neg u l]
      have hlam0 : 0 ≤ u / (u - l) := div_nonneg hu.le (by linarith)
      have hlam1 : u / (u - l) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hend : u + -(u / (u - l) * u) = -(u / (u - l) * l) := by
        field_simp; ring
      simp only [not_lt.mpr hl0.le, not_le.mpr hu, not_le.mpr hl0, if_false,
        min_eq_right hlam1, max_eq_right hlam0, hend, max_self]
      refine ⟨trivial, ?_, ?_⟩ <;> field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
