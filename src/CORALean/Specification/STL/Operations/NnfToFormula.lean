import CORALean.Specification.STL.Definitions.Nnf
import CORALean.Specification.STL.STL

/-!
# A normal form as an STL formula

[1, Lemma 4]: `n.toFormula` is the STL formula with natural bounds a negation normal form stands
for.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The STL formula of `n`. -/
def STL.Nnf.toFormula : STL.Nnf X → STL.Formula X
  | .lit ϱ => .ofPform ϱ
  | .and φ ψ => (φ.toFormula).and ψ.toFormula
  | .or φ ψ => .or φ.toFormula ψ.toFormula
  | .until i j φ ψ => .until i j φ.toFormula ψ.toFormula
  | .release i j φ ψ => .release i j φ.toFormula ψ.toFormula


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
