module

public import CORALean.ContSet.Interval.Real.Theorems.CoshExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `cosh` encloses it

If the operand's interval encloses its value, the interval `Interval.cosh` stores at the `cosh`
node encloses the node's value, exactly (`Interval.cosh_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `cosh` node encloses its function. -/
theorem SyntaxTree.encloses_cosh (h : Encloses B t) : Encloses B t.cosh :=
  fun x hx =>
  have hc := h x hx
  have hne : t.value.inf 0 ≤ t.value.sup 0 := hc.1.trans hc.2
  contains_of_image (f := Real.cosh)
    (Real.Interval.cosh_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact hne)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
