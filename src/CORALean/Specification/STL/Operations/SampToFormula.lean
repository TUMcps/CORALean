module

public import CORALean.Specification.STL.Definitions.Samp
public import CORALean.Specification.STL.STL
public import CORALean.Specification.STL.Operations.Basic

@[expose] public section

/-!
# A sampled time formula as an STL formula

[1, Sec. 4.1]: `s.toFormula c` is the formula with time step `c`: `X_c` is `Xₐ` at `a = c`, and
`F(0,c)`, `G(0,c)` the window operators.

Real-only, a specification: it rewrites or builds formulas, whose time bounds and constants are
part of the syntax and are copied or added exactly, never rounded.

## Inputs
* `c` – time step

## Output
* the STL formula of the sampled time formula

## References

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../../references/2016/roehm-atva-stl-model-checking.md)
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
