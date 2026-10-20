module

public import CORALean.ContSet.Interval.Real.Theorems.SinExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `sin` encloses it

If the operand's interval encloses its value, the interval `Interval.sin` stores at the `sin` node
encloses the node's value, exactly (`Interval.sin_exact`).

## Inputs
* none

## Hypotheses
* `h` – the operand's interval encloses its function

## Conclusion
* the interval of the sine encloses its function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `sin` node encloses its function. -/
theorem SyntaxTree.encloses_sin (h : Encloses B t) : Encloses B t.sin :=
  fun x hx =>
  have hc := h x hx
  have hne : t.value.inf 0 ≤ t.value.sup 0 := hc.1.trans hc.2
  contains_of_image (f := Real.sin)
    (Real.Interval.sin_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact hne)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
