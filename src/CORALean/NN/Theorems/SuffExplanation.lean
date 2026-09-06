import CORALean.ContSet.Interval.Real.Instances
import CORALean.NN.NeuralNetwork
import CORALean.NN.Operations.ExplainBox

/-!
# Sufficient explanation

`def:suff-explanation` [1]: pin `E` to `x`'s values and let the rest range over
`explainBox`; `l` must keep strictly beating every rival everywhere in it. `l`
stands for `argmax_j nn(x)_j`, exactly as it does in `NeuralNetwork.classifies`.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E` is sufficient for `nn`'s classification of `x` as `l`: fixing `E`, `l`
still beats every rival everywhere in the `ε`-box around the rest. -/
def NeuralNetwork.IsSuffExplanation (nn : NeuralNetwork S n m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) : Prop :=
  ∀ x', x' ∈ construct (explainBox x ε E) → ∀ j, j ≠ l → nn.eval x' j < nn.eval x' l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
