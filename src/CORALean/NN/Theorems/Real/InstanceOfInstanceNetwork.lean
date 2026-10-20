module

public import CORALean.NN.Definitions.ReducibleNetwork

@[expose] public section

/-!
# An instance network computes an instance

ℝ-only, as `InstanceNetwork` is: its biases are real, and only at `𝕋 := ℝ` does a network of
layers store them. What it adds to `Instance` is the network itself, which `ReducesAt` needs and
nothing else does; forgetting it is this, one constructor at a time, the map unchanged.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* an instance network computes an instance

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [Real.IntervalOuter S] [Real.OfInterval S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A network `Φ` stands for, read as the map it computes: what the soundness theorems of
[1, Alg. 2] and [1, Alg. 3] take, written once over the scalar. -/
theorem instance_of_instanceNetwork : ∀ {n m : ℕ} {Φ : ReducibleNetwork ℝ n m}
    {nn : NeuralNetwork S n m} {f : Vec ℝ n → Vec ℝ m}, Φ.InstanceNetwork nn f → Φ.Instance f
  | _, _, _, _, _, .nil hf => .nil hf
  | _, _, _, _, _, .cons hR hc hrest hf => .cons hR hc (instance_of_instanceNetwork hrest) hf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
