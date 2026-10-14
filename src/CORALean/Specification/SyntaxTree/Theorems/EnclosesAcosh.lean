module

public import CORALean.ContSet.Interval.Real.Theorems.AcoshExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `acosh` encloses it

If the operand's interval encloses its value, the interval `Interval.acosh` stores at the `acosh`
node encloses the node's value for an operand `≥ 1`, exactly (`Interval.acosh_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `acosh` node encloses its function for an operand `≥ 1`. -/
theorem SyntaxTree.encloses_acosh (h : Encloses B t) (hd : 1 ≤ t.value.inf 0) : Encloses B t.acosh
    :=
  fun x hx =>
  have hc := h x hx
  have hne : t.value.inf 0 ≤ t.value.sup 0 := hc.1.trans hc.2
  contains_of_image (f := Real.arcosh)
    (Real.Interval.acosh_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact ⟨hd, hd.trans hne⟩)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
