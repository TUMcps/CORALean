module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.IsSound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# A sound tree encloses its function

`IsSound` holds the enclosure of the root, whichever the root.

## Inputs
* none

## Hypotheses
* `h` – the tree is sound over the box

## Conclusion
* the tree encloses its function over the box
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sound tree encloses its function over the box. -/
theorem SyntaxTree.encloses_of_isSound (h : IsSound B t) : -- --- CONCL ---
    t.Encloses B := by -- --- PROOF ---
  cases t with
  | var i v => exact fun x hx => h x hx
  | unary op v f t => exact h.2.1
  | binary op v f t₁ t₂ => exact h.2.2.1
  | numLeft op v f c t => exact h.2.1
  | numRight op v f t c => exact h.2.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
