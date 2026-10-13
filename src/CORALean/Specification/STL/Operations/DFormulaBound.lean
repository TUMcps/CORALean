module

public import CORALean.Specification.STL.Definitions.DiscreteFormula

@[expose] public section

/-!
# `STL.DFormula.bound`

[1, Sec. II-B (bound)]: the bound of a bounded-time formula, the maximum over the sums of all
nested upper bounds of its temporal operators, `□[0,10] □[1,6] φ` having `10 + 6 = 16`. One step
per operator, so it takes time linear in the length of the formula.

## References

* [1] V. Raman, A. Donzé, M. Maasoumy, R. M. Murray, A. Sangiovanni-Vincentelli and
      S. A. Seshia. "Model Predictive Control with Signal Temporal Logic Specifications". In
      Proc. of the 53rd IEEE Conference on Decision and Control (CDC), pp. 81-87, 2014.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound of `φ`: a predicate reads one step, a temporal operator adds its upper bound. -/
def STL.DFormula.bound : STL.DFormula X → ℕ
  | .pred _ => 0
  | .npred _ => 0
  | .and φ ψ => max φ.bound ψ.bound
  | .or φ ψ => max φ.bound ψ.bound
  | .always _ b _ φ => b + φ.bound
  | .eventually _ b _ φ => b + φ.bound
  | .until _ b _ φ ψ => b + max φ.bound ψ.bound

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
