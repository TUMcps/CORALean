import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

/-!
# `HPolytope.plusOf`

CORA's `plus` on halfspace descriptions. Not exact, and it cannot be: the sum's
facet normals are generally none of either summand's, so they would have to be
enumerated first. Instead the caller names the directions and each row's bound
is the two summands' extents in that direction, added.

Exact when the directions happen to contain the sum's facet normals, which is
what enumeration would have produced — so the enumeration is a precision
question, not a soundness one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {P₁ P₂ : HPolytope α}

def HPolytope.plusOf (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => (u₁ i).add (u₂ i)

end CORALean.Real
