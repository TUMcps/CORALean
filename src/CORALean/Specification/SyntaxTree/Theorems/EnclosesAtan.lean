module

public import CORALean.ContSet.Interval.Real.Theorems.AtanExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `atan` encloses it

If the operand's interval encloses its value, the interval `Interval.atan` stores at the `atan`
node encloses the node's value, exactly (`Interval.atan_exact`).

## Inputs
* none

## Hypotheses
* `h` – the operand's interval encloses its function

## Conclusion
* the interval of the inverse tangent encloses its function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `atan` node encloses its function. -/
theorem SyntaxTree.encloses_atan (h : Encloses B t) : Encloses B t.atan :=
  fun x hx =>
  have hc := h x hx
  contains_of_image (f := Real.arctan)
    (Real.Interval.atan_exact _) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
