module

public import CORALean.ContSet.Interval.Real.Theorems.AsinExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `asin` encloses it

If the operand's interval encloses its value, the interval `Interval.asin` stores at the `asin`
node encloses the node's value for an operand inside `[-1,1]`, exactly (`Interval.asin_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `asin` node encloses its function for an operand inside `[-1,1]`. -/
theorem SyntaxTree.encloses_asin (h : Encloses B t) (hd₁ : -1 ≤ t.value.inf 0) (hd₂ : t.value.sup 0
    ≤ 1) : Encloses B t.asin :=
  fun x hx =>
  have hc := h x hx
  have hne : t.value.inf 0 ≤ t.value.sup 0 := hc.1.trans hc.2
  contains_of_image (f := Real.arcsin)
    (Real.Interval.asin_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact ⟨⟨hd₁, hne.trans hd₂⟩, ⟨hd₁.trans hne, hd₂⟩⟩)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
