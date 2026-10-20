module

public import CORALean.ContSet.Interval.Real.Theorems.LogExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `log` encloses it

If the operand's interval encloses its value, the interval `Interval.log` stores at the `log` node
encloses the node's value for a positive operand, exactly (`Interval.log_exact`).

## Inputs
* none

## Hypotheses
* `h` – the operand's interval encloses its function
* `hd` – the operand is positive

## Conclusion
* the interval of the logarithm encloses its function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `log` node encloses its function for a positive operand. -/
theorem SyntaxTree.encloses_log (h : Encloses B t) (hd : 0 < t.value.inf 0) : Encloses B t.log :=
  fun x hx =>
  have hc := h x hx
  have hne : t.value.inf 0 ≤ t.value.sup 0 := hc.1.trans hc.2
  contains_of_image (f := Real.log)
    (Real.Interval.log_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact ⟨hd, hd.trans_le hne⟩)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
