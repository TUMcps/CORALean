module

public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.NN.NeuralNetwork
public import CORALean.NN.Operations.ExplainBox

@[expose] public section

/-!
# Sufficient explanation

[1, Def. 1]: pin `E` to `x`'s values and let the rest range over `explainBox`;
`l` must keep strictly beating every rival everywhere in it. `l` stands for
`argmax_j nn(x)_j`, exactly as it does in `NeuralNetwork.classifies`.

## Inputs
* `f` – network function
* `x` – input point
* `ε` – perturbation radius
* `E` – candidate explanation, a feature set
* `l` – target label

## Output
* with E fixed, the target label strictly beats every rival on the whole box

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning, 2025.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `E` is sufficient for `f`'s classification of `x` as `l`: fixing `E`, `l`
still beats every rival everywhere in the `ε`-box around the rest. Stated of the
exact map, which a network is sound at rather than stores. -/
def IsSuffExplanation (f : Vec ℝ n → Vec ℝ m) (x : Vec ℝ n) (ε : ℝ)
    (E : Finset (Fin n)) (l : Fin m) : Prop :=
  ∀ x', x' ∈ construct (explainBox x ε E) → ∀ j, j ≠ l → f x' j < f x' l

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
