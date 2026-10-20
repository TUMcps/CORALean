module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.domain`

The definition is [1, Def. 7].

The coefficients the representation admits, split from the map they go through so that the set can
be read as an image. Both blocks of factors travel together, as one point of a product, because
the constraint couples the dependent ones. No `HPolytope` here, unlike `ConZonotope.domain`: the
constraint is polynomial in the factors, so closedness comes from the continuity of a monomial.

## Inputs
* `cPZ` – constrained polynomial zonotope

## Output
* admissible factor and coefficient vectors

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The admissible factor and coefficient vectors: the unit cube of the independent half, and the
constraint on the dependent half, whose own domain is the other cube (`cons_dom`). -/
def ConPolyZono.domain (cPZ : ConPolyZono α) : Set ((Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ)) :=
  {ab | (∀ j, |ab.2 j| ≤ 1) ∧ ab.1 ∈ cPZ.cons.construct}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
