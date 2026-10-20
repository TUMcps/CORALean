module

public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.Global.SupportFunction.Composition

@[expose] public section

/-!
# `HPolytope.plusOf`

CORA's `plus` on halfspace descriptions. Not exact, and it cannot be: the sum's facet normals
are generally none of either summand's, so they would have to be enumerated first. Instead the
caller names the directions and each row's bound is the two summands' extents in that
direction, added. Exact when the directions contain the sum's facet normals, so the enumeration
is a precision question, not a soundness one.

[1, Prop. 4] is this at the summand's own rows, the other summand's support values added on.

## Inputs
* `Aq` – family indexed by `Fin q`
* `u₁` – a support bound of `P₁.construct` along each row
* `u₂` – a support bound of `P₂.construct` along each row

## Output
* the polytope on the directions `Aq` bounded by the sum of the bounds `u₁` and `u₂`
## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ} {P₁ P₂ : HPolytope α}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.plusOf (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u₁ : ∀ i, SupportBound P₁.construct (Aq i))
    (u₂ : ∀ i, SupportBound P₂.construct (Aq i)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => (u₁ i).add (u₂ i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
