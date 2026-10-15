module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.minkDiffStretch`

The generator representation [1, Thm. 4], [1, Thm. 5] and [1, Prop. 6] all
return: the centers subtracted, and each generator of the minuend stretched by
its own factor `μ`. They differ only in what picks `μ` — a linear program
pushing it up until the halfspaces of the stretched minuend sit inside those of
the difference, one pushing it down until they sit outside, or (22) solved
exactly — so the operation is shared and the direction lives on the theorems.

`μ` is an argument, not computed here. [1]'s own `μ*` is an optimum, and an
optimum is a choice of objective (`ζ`, "a user-specified vector") on top of the
constraint; `minkDiffStretch_inner` and `minkDiffStretch_outer` ask only for
the constraint, so any feasible `μ` — optimal or not — carries the guarantee.

Not a `MinkDiff` instance. Feasibility of `μ` is a fact about the particular
pair of operands together with a halfspace description of the minuend, and
`minkDiff : S → S → S` has no slot for either.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
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
