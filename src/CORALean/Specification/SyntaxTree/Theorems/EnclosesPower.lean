module

public import CORALean.ContSet.Interval.Real.Theorems.PowerExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of a power encloses it

If the operand's interval encloses its value, `Interval.power` encloses the power
(`Interval.power_exact`).

## Inputs
* `k` – exponent

## Hypotheses
* `h` – the operand's interval encloses its function

## Conclusion
* the interval of the power encloses its function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the power node encloses its function. -/
theorem SyntaxTree.encloses_power (h : Encloses B t) (k : ℕ) : Encloses B (t.power k) := fun x hx =>
  have hc := h x hx
  contains_of_image (f := fun y => y ^ k)
    (Real.Interval.power_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact hc.1.trans hc.2) k) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
