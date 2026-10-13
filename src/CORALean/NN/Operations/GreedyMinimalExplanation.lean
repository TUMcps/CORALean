module

public import CORALean.NN.Operations.GreedyExplanationStep
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# [1, Alg. 1]: greedy minimal explanation search, at a sufficiency oracle

Every `suff(...)` call in the printed algorithm is decided by an external
neural network verifier — an NP-complete query in general (§2.3) — never
formalized as a computation here. `greedyMinimalExplanation` instead takes
that decision as an oracle `suff : Finset (Fin n) → Bool`, sound at any oracle
shown correct at `IsSuffExplanation`, not only at one CORALean itself could certify.

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

/-- `[n]`, then each feature dropped in turn whenever the oracle still calls
the result sufficient. -/
def greedyMinimalExplanation (n : ℕ) (suff : Finset (Fin n) → Bool) : Finset (Fin n) :=
  (List.finRange n).foldl (greedyExplanationStep suff) Finset.univ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
