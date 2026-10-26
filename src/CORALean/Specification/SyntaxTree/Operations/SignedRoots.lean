module

public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Operations.Interval

@[expose] public section

/-!
# The sign an operand's interval allows

In `aux_power_` (even exponent) and `aux_cosh_` the two solutions `±r` of `x² = r²` meet the
interval
`intPrev` of the operand: both if it contains `0` (`[-m, m]`), the positive one if it is
nonnegative, the
negative one otherwise. `preInf` and `preSup` are the roots of the two bounds of the target.

Real-only, a specification: it computes with real numbers exactly; its rounded refinement is
`SyntaxTree.signedRootsFloat`.

## Inputs
* `prev` – previous interval
* `preInf` – lower root
* `preSup` – upper root

## Output
* the interval of signed roots the previous interval allows
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The interval of the solutions `±r` with `r` between `preInf` and `preSup` that `intPrev` allows.
-/
noncomputable def SyntaxTree.signedRoots (prev : Dom) (preInf preSup : ℝ) : Dom :=
  if 0 < prev.sup 0 ∧ prev.inf 0 < 0 then
    let m := max preInf preSup
    interval (-m) m
  else if 0 < prev.sup 0 then interval (min preInf preSup) (max preInf preSup)
  else interval (-(max preInf preSup)) (-(min preInf preSup))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
