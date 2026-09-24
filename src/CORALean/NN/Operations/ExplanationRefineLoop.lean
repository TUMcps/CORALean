import CORALean.Global.Tensor

/-!
# [1, Alg. 2, l. 4-19]: the refinement loop answering one query

The do-while that replaces [1, Alg. 1]'s `suff` call: pass at the current abstraction level, fail
on a genuine counterexample, and otherwise refine one level and repeat. Neither oracle is
computed, for [1, Alg. 1]'s reason.

## References

* [1] S. Bassan, Y. Y. Elboher, T. Ladner, M. Althoff and G. Katz. "Explaining
      Fast and Slow: Abstraction and Refinement of Provable Explanations".
      ICML 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2, l. 4-19]: the do-while at candidate set `E`, entered at
abstraction level `k` with `r` refinements still to spend. -/
def explanationRefineLoop (absSuff genuine : ℕ → Finset (Fin n) → Bool) (E : Finset (Fin n)) :
    ℕ → ℕ → Bool
  | k, 0 => absSuff k E
  | k, r + 1 =>
      if absSuff k E then true
      else if genuine k E then false
      else explanationRefineLoop absSuff genuine E (k + 1) r

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
