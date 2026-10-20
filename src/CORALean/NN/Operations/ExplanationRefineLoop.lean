module

public import Mathlib.Data.Finset.Defs

@[expose] public section

/-!
# [1, Alg. 2, l. 4-19]: the refinement loop answering one query

The do-while that replaces [1, Alg. 1]'s `suff` call: pass at the current abstraction level, fail
on a genuine counterexample, and otherwise refine one level and repeat. Neither oracle is
computed, for [1, Alg. 1]'s reason.

## Inputs
* `absSuff` – abstract sufficiency check at each level
* `genuine` – genuine counterexample check at each level
* `E` – candidate explanation

## Output
* whether the candidate is sufficient after the refinement loop

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

/-- [1, Alg. 2, l. 4-19]: the do-while at candidate set `E`, entered at
abstraction level `k` with `r` refinements still to spend. -/
def explanationRefineLoop (absSuff genuine : ℕ → Finset (Fin n) → Bool) (E : Finset (Fin n)) :
    ℕ → ℕ → Bool
  -- 5. the last pass of the `do`, with no refinement left: only `suff(f′, x, S∖{i}, ϵp)` counts
  | k, 0 => absSuff k E
  | k, r + 1 =>
      -- 5. `if suff(f′, x, S∖{i}, ϵp) then S ← S∖{i}; break`, `f′` at abstraction level `k`
      if absSuff k E then true
      -- 8. `x̃ ← obtain counterexample`, 9. `if arg maxⱼ f(x̃)(j) ≠ t then F ← F∖{i}; break`
      else if genuine k E then false
      -- 12. `f″ ← Refine f′` (Prop. 2), 13. `f′ ← f″`, 16. `while true`: the next pass
      else explanationRefineLoop absSuff genuine E (k + 1) r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
