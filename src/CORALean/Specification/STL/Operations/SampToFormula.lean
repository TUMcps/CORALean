import CORALean.Specification.STL.Definitions.Samp
import CORALean.Specification.STL.STL

/-!
# A sampled time formula as an STL formula

[1, Sec. 4.1]: `s.toFormula c` is the formula with time step `c`: `X_c` is `Xₐ` at `a = c`, and
`F(0,c)`, `G(0,c)` the window operators.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The STL formula of `s` at time step `c`. -/
def STL.Samp.toFormula (c : ℝ≥0) : STL.Samp X → STL.Formula X
  | .lit ϱ => .ofPform ϱ
  | .not s => .not (s.toFormula c)
  | .and s t => (s.toFormula c).and (t.toFormula c)
  | .or s t => .or (s.toFormula c) (t.toFormula c)
  | .next s => .next c (s.toFormula c)
  | .fin ϱ => .finOpen c (.ofPform ϱ)
  | .glob ϱ => .globOpen c (.ofPform ϱ)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
