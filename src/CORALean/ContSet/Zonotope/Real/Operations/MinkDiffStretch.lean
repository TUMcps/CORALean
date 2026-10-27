module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.minkDiffStretch`

The generator representation [1, Thm. 4], [1, Thm. 5] and [1, Prop. 6] all return: the centers
subtracted, and each generator of the minuend stretched by its own factor `μ`. They differ only
in what picks `μ` — a linear program pushing it up until the halfspaces of the stretched minuend
sit inside those of the difference, one pushing it down until they sit outside, or (22) solved
exactly — so the direction lives on the theorems. `μ` is an argument: [1]'s `μ*` is an optimum,
a choice of objective on top of the constraint, and `minkDiffStretch_inner` and `_outer` ask only
for the constraint. Not a `MinkDiff` instance: feasibility of `μ` is a fact about the particular
pair together with a halfspace description of the minuend.

## Inputs
* `Z₁` – minuend
* `Z₂` – subtrahend
* `μ` – generator stretch factors

## Output
* minuend with stretched generators and shifted center

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(c⁽ᵐ⁾ - c⁽ˢ⁾, Ĝ⁽ᵐ⁾µ)`, the generator representation [1, Thm. 4] and
[1, Thm. 5] share. -/
def Zonotope.minkDiffStretch (Z₁ Z₂ : Zonotope α) (μ : Fin Z₁.h → ℝ) : Zonotope α where
  h := Z₁.h
  c := Z₁.c - Z₂.c
  G := fun i => μ i • Z₁.G i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
