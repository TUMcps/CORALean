import CORALean.NN.Layers.Definitions.Softmax

/-!
# Softmax's denominator is positive

A coordinate is what makes the denominator positive, so every statement about softmax takes one
rather than a `NeZero`: at `n = 0` there is nothing to say and the layer's obligation is vacuous.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem exp_sum_pos (x : Vec ℝ n) (i : Fin n) : 0 < ∑ j, Real.exp (x j) :=
  Finset.sum_pos (fun j _ => Real.exp_pos (x j)) ⟨i, Finset.mem_univ i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
