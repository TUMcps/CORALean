module

public import CORALean.NN.Layers.Theorems.ReluRelaxationSound
public import CORALean.NN.Layers.Theorems.Real.DeepZReluEq

@[expose] public section

/-!
# DeepZ's ReLU transformer is sound

[1, Thm. 3.1]: Eq. (5) encloses ReLU on every box, `|ReLU(t) - (λ t + μ)| ≤ μ`. At ℝ it is
the tree's `reluRelaxation reluSlope` (`deepZRelu_eq_reluRelaxation`), whose soundness is
stated once for every scalar; a box is nonempty whenever it holds a point, which is all the
equality needs.

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

theorem deepZRelu_sound : deepZRelu.Sound relu := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  have h := (reluRelaxation_sound (𝕋 := ℝ) reluSlope).sound hl hu
  change l ≤ t at hl
  change t ≤ u at hu
  change |relu t - ((reluRelaxation reluSlope).slope l u * t
    + (reluRelaxation reluSlope).offset l u)| ≤ (reluRelaxation reluSlope).error l u at h
  obtain ⟨hs, ho, he⟩ := deepZRelu_eq_reluRelaxation (le_trans hl hu)
  show |relu t - (deepZRelu.slope l u * t + deepZRelu.offset l u)| ≤ deepZRelu.error l u
  rw [hs, ho, he]
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
