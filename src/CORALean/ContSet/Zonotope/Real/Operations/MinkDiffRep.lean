module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.minkDiffRep`

CORA's default `'approx'` scales the minuend's generators to fit halfspaces the subtrahend's
support has shifted inward, [1, Thm. 3]. Two things stop that from being adopted: the scaling is
a pseudoinverse solution checked by nothing, and the argument needs the halfspaces to *equal* the
minuend, which only its own facet normals do. So the difference is computed from a generator
representation instead. `M`, writing each subtrahend generator in the minuend's own, is the
candidate and the two conditions are its check, as `HPolytope.supportBound` checks a simplex's
weighting — a wrong `M` yields `none`. The budget decouples per generator, so `1 - ∑ⱼ |Mᵢⱼ|` is
the largest the check admits, and at `G₂ = diag(μ) G₁` it is `minkDiffAligned` again.

## Inputs
* `Z₁` – minuend
* `Z₂` – subtrahend
* `M` – generator representation matrix

## Output
* difference zonotope, or none if `M` fails

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The difference at a checked generator representation `M`, and `none` where
`M` is not one or leaves a row of the minuend no room. -/
noncomputable def Zonotope.minkDiffRep (Z₁ Z₂ : Zonotope α) (M : Fin Z₁.h → Fin Z₂.h → ℝ) :
    Option (Zonotope α) :=
  if (∀ j, Z₂.G j = ∑ i, M i j • Z₁.G i) ∧ ∀ i, ∑ j, |M i j| ≤ 1 then
    some { h := Z₁.h, c := Z₁.c - Z₂.c, G := fun i => (1 - ∑ j, |M i j|) • Z₁.G i }
  else none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
