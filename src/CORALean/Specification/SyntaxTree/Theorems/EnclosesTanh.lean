module

public import CORALean.ContSet.Interval.Real.Theorems.TanhExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `tanh` encloses it

If the operand's interval encloses its value, the interval `Interval.tanh` stores at the `tanh`
node encloses the node's value, exactly (`Interval.tanh_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `tanh` node encloses its function. -/
theorem SyntaxTree.encloses_tanh (h : Encloses B t) : Encloses B t.tanh :=
  fun x hx =>
  have hc := h x hx
  contains_of_image (f := Real.tanh)
    (Real.Interval.tanh_exact _) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
