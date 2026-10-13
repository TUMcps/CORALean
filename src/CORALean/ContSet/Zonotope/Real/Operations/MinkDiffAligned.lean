module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.minkDiffAligned`

CORA's exact case of `@zonotope/minkDiff`, [1, Prop. 5]: two zonotopes with the
same generator count, `Z₂`'s each a scaled copy of `Z₁`'s own, need no
enclosure at all — `c₁ - c₂` and `G₁ - G₂` already suffice. `hh` only lines the
two counts up; the alignment witness itself is what `minkDiffAligned_inner`
asks a `μ` for.

Not a `MinkDiff` instance: unlike `Ellipsoid.plus`'s scalings, fixed once for
the whole type, `hh` is a fact about the *particular* pair of operands, so
there is no way to make `minkDiff : S → S → S` total over it — the field has
no argument slot for a hypothesis at all.

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

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `c₁ - c₂` and `G₁ - G₂`, [1, Prop. 5]'s exact solution for aligned
generators. `hh` casts `Z₂`'s generators against `Z₁`'s own index. -/
def Zonotope.minkDiffAligned (Z₁ Z₂ : Zonotope α) (hh : Z₁.h = Z₂.h) : Zonotope α where
  h := Z₁.h
  c := Z₁.c - Z₂.c
  G := fun i => Z₁.G i - Z₂.G (Fin.cast hh i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
