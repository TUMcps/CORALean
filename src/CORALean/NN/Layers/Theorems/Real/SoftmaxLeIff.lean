module

public import CORALean.NN.Layers.Definitions.Softmax

@[expose] public section

/-!
# Softmax keeps the order of its inputs

All outputs share the denominator `∑ exp (x k) > 0`, and `exp` is strictly monotone, so output
`j` is at most output `i` exactly when input `j` is at most input `i`. A classification that
compares the outputs of a final softmax can compare its inputs instead: CORA.cpp's verifier drops
an output softmax for that reason.

## Inputs
* `x` – input vector
* `i` – first coordinate
* `j` – second coordinate

## Hypotheses
* none

## Conclusion
* `softmax x j ≤ softmax x i` if and only if `x j ≤ x i`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmax_le_iff (x : Vec ℝ n) (i j : Fin n) :
    softmax x j ≤ softmax x i ↔ x j ≤ x i := by
  have hS : 0 < ∑ k, Real.exp (x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos (x k)) ⟨i, Finset.mem_univ i⟩
  show Real.exp (x j) / _ ≤ Real.exp (x i) / _ ↔ _
  rw [div_le_div_iff_of_pos_right hS, Real.exp_le_exp]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
