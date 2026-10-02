import CORALean.Global.Tensor
import Mathlib.Data.Finset.SDiff

/-!
# [1, Alg. 1]'s loop body

One feature considered for dropping: the oracle decides, and the candidate set shrinks only if
it says the smaller set is still sufficient.

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

/-- [1, Alg. 1, l. 3-5]: drop `i` from `E` when the oracle says the result
stays sufficient, otherwise keep `E` as it is. -/
def greedyExplanationStep (suff : Finset (Fin n) → Bool) (E : Finset (Fin n)) (i : Fin n) :
    Finset (Fin n) :=
  if suff (E \ {i}) then E \ {i} else E

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
