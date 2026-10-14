module

public import CORALean.ContSet.Interval.Real.Theorems.AsinhExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `asinh` encloses it

If the operand's interval encloses its value, the interval `Interval.asinh` stores at the `asinh`
node encloses the node's value, exactly (`Interval.asinh_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `asinh` node encloses its function. -/
theorem SyntaxTree.encloses_asinh (h : Encloses B t) : Encloses B t.asinh :=
  fun x hx =>
  have hc := h x hx
  contains_of_image (f := Real.arsinh)
    (Real.Interval.asinh_exact _) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
