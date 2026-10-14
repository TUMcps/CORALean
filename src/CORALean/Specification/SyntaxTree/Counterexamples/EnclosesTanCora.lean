module

public import CORALean.ContSet.Interval.Real.Theorems.TanExact
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.Counterexamples.TanCora
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.ContainsOfImage

@[expose] public section

/-!
# The interval of `tan`, as printed encloses it

If the operand's interval encloses its value, the interval `Interval.tan` stores at the `tan`, as
printed node encloses the node's value for an operand inside `(-pi/2, pi/2)`, exactly
(`Interval.tan_exact`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interval of the `tan`, as printed node encloses its function for an operand inside `(-pi/2,
pi/2)`. -/
theorem SyntaxTree.encloses_tanCora (h : Encloses B t) (hd₁ : -(Real.pi / 2) < t.value.inf 0)
    (hd₂ : t.value.sup 0 < Real.pi / 2) : Encloses B t.tanCora :=
  fun x hx =>
  have hc := h x hx
  have hne : t.value.inf 0 ≤ t.value.sup 0 := hc.1.trans hc.2
  contains_of_image (f := Real.tan)
    (Real.Interval.tan_exact _ (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact ⟨⟨hd₁, hne.trans_lt hd₂⟩, ⟨hd₁.trans_le hne, hd₂⟩⟩)) hc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
