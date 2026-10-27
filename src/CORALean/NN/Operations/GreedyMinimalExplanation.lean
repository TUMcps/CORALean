module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.SDiff
public import CORALean.Global.StepOf

@[expose] public section

/-!
# [1, Alg. 1]: greedy minimal explanation search, at a sufficiency oracle

Every `suff(...)` call in the printed algorithm is decided by an external
neural network verifier — an NP-complete query in general (§2.3) — never
formalized as a computation here. `greedyMinimalExplanation` instead takes
that decision as an oracle `suff : Finset (Fin n) → Bool`, sound at any oracle
shown correct at `IsSuffExplanation`, not only at one CORALean itself could certify.

## Inputs
* `n` – number of features
* `suff` – sufficiency oracle

## Output
* feature set with every droppable feature removed

## References

* [1] [S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining, Fast and Slow:
      Abstraction and Refinement of Provable Explanations". Proceedings of the 42nd International
      Conference on Machine Learning,
      2025.](../../../../references/2025/bassan-icml-explaining-fast-and-slow.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- [1, Alg. 1, l. 3-5]: drop `i` from `E` when the oracle says the result
stays sufficient, otherwise keep `E` as it is. -/
@[step_of greedyMinimalExplanation]
def step_greedyExplanationStep (suff : Finset (Fin n) → Bool) (E : Finset (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  -- 4. `S ∖ {i}`, the candidate with feature `i` dropped
  let S' := E \ {i}
  -- 3. `if suff(f, x, S∖{i}, ϵp) then S ← S∖{i}`
  if suff S' then S' else E


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[n]`, then each feature dropped in turn whenever the oracle still calls
the result sufficient. -/
def greedyMinimalExplanation (n : ℕ) (suff : Finset (Fin n) → Bool) : Finset (Fin n) :=
  -- 1. `S ← [n]`, 2. `for each feature i`: lines 3-5 are the step above, 6. `return S`
  (List.finRange n).foldl (step_greedyExplanationStep suff) Finset.univ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
