module

public import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

@[expose] public section

/-!
# `ConPolyZono.domain`

The definition is [1, Def. 7].

The coefficients the representation admits, split from the map they go
through so that the set can be read as an image. Both blocks of factors
travel together, as one point of a product, because the constraint couples
the dependent ones.

No `HPolytope` here, unlike `ConZonotope.domain`: the constraint is polynomial
in the factors, so what makes this domain closed is the continuity of a monomial
and not a halfspace description.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The admissible factor and coefficient vectors: the two unit cubes, cut down
by the constraint on the dependent half. -/
def ConPolyZono.domain (cPZ : ConPolyZono α) : Set ((Fin cPZ.p → ℝ) × (Fin cPZ.qI → ℝ)) :=
  {ab | (∀ k, |ab.1 k| ≤ 1) ∧ (∀ j, |ab.2 j| ≤ 1) ∧ cPZ.satisfies ab.1}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
