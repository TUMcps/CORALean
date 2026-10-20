module

public import CORALean.ContSet.Interval.Real.Theorems.SinhExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `sinh` encloses it

If the operand's interval encloses its value, the interval `Interval.sinh` stores at the `sinh`
node encloses the node's value, exactly (`Interval.sinh_exact`).

## Inputs
* none

## Hypotheses
* `h` – the operand's interval encloses its function

## Conclusion
* the interval of the hyperbolic sine encloses its function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `sinh` node encloses its function. -/
theorem SyntaxTree.encloses_sinh (h : Encloses B t) : Encloses B t.sinh :=
  fun x hx =>
  have hc := h x hx
  contains_of_image (f := Real.sinh)
    (Real.Interval.sinh_exact _) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
