module

public import CORALean.NN.Operations.ExplanationRefineLoop
public import CORALean.NN.Operations.GreedyMinimalExplanation

@[expose] public section

/-!
# [1, Alg. 2]: the abstraction-refinement search

[1, Alg. 2] is [1, Alg. 1] with one substitution: each `suff` call is answered
by the do-while of l. 4-19 instead of by a query on `f`, so
`greedyAbstractExplanation` is `greedyMinimalExplanation` at that composite
oracle and inherits its correctness once the oracle is shown exact.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: [1, Alg. 1]'s loop, every `suff` call answered by the refinement
loop entered at the coarsest level with `N` refinements to spend. -/
def greedyAbstractExplanation (n : ℕ) (absSuff genuine : ℕ → Finset (Fin n) → Bool) (N : ℕ) :
    Finset (Fin n) :=
  -- 1. `S ← [n]`, 2. `for each feature i`, 18. `return S`; 3-16: `suff` is the refinement loop
  greedyMinimalExplanation n fun E => explanationRefineLoop absSuff genuine E 0 N

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
