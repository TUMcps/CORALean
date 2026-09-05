import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.domain` and `ConPolyZono.affine`

The coefficients the representation admits and the map it sends them through,
split apart so that the set can be read as an image. Both blocks of factors
travel together, as one point of a product, because the constraint couples the
dependent ones while the map reads both.

No `HPolytope` here, unlike `ConZonotope.domain`: the constraint is polynomial
in the factors, so what makes this domain closed is the continuity of a monomial
and not a halfspace description.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The admissible factor and coefficient vectors: the two unit cubes, cut down
by the constraint on the dependent half. -/
def ConPolyZono.domain (C : ConPolyZono α) : Set ((Fin C.p → ℝ) × (Fin C.q → ℝ)) :=
  {ab | (∀ k, |ab.1 k| ≤ 1) ∧ (∀ j, |ab.2 j| ≤ 1) ∧ C.satisfies ab.1}

/-- The map onto the set, affine in the independent half and polynomial in the
dependent one. -/
def ConPolyZono.affine (C : ConPolyZono α) (ab : (Fin C.p → ℝ) × (Fin C.q → ℝ)) : α :=
  C.c + ∑ i, PolyZonotope.monomial C.E ab.1 i • C.G i + ∑ j, ab.2 j • C.GI j

end CORALean.Real
