import CORALean.ContSet.HPolytope.Float.Operations.IntersectionExact
import CORALean.HybridDynamics.Definitions.Transition

/-!
# `Transition.convGuard`

CORA's `convGuard` at `options.guardIntersect = 'polytope'`: the guard is replaced by its
exact intersection with the location's invariant, both polytopes, so that a later guard
intersection already respects the invariant. The stacked-rows `HPolytope.intersection` is
generic over the scalar, so this runs at any float and at `ℝ`.

Not modelled: the `'conZonotope'` branch, which converts a polytope guard to a conZonotope and
leaves the invariant alone, and the conversion of a non-polytope guard to a polytope.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The transition with its polytope guard cut to the invariant `inv`. -/
def Transition.convGuard (e : Transition (HPolytope 𝕋) L 𝕋 n) (inv : HPolytope 𝕋 n) :
    Transition (HPolytope 𝕋) L 𝕋 n :=
  { e with guard := HPolytope.intersection e.guard inv }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
