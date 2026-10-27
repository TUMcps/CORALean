module

public import CORALean.Specification.STL.Definitions.RTL

@[expose] public section

/-!
# Finally in RTL

`F[a,b] ψ := true U[a,b] ψ` of [1, Def. 2], with `true` as `A ⊤`.

Real-only, a specification: it rewrites or builds formulas, whose time bounds and constants are
part of the syntax and are copied or added exactly, never rounded.

## Inputs
* `a` – interval lower bound
* `b` – interval upper bound
* `ψ` – formula

## Output
* the formula holds at some time of the interval

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

/-- `F[a,b] ψ`. -/
def RTL.Formula.finally (a b : ℝ≥0) (ψ : RTL.Formula X) : RTL.Formula X :=
  .until a b (.A Pform.top) ψ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
