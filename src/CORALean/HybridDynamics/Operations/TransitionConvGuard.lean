module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.HybridDynamics.Definitions.Transition
public import CORALean.ContSet.HPolytope.Float.Operations.Intersection

@[expose] public section

/-!
# `Transition.convGuard`

CORA's `convGuard` at `options.guardIntersect = 'polytope'`: the guard is replaced by its
intersection with the location's invariant, both polytopes, so that a later guard
intersection already respects the invariant. `HPolytope.intersection` stacks the rows after
folding each polytope's error box into them, so the result contains the intersection; it is
generic over the scalar, so this runs at any float and at `ℝ`.

Not modelled: the `'conZonotope'` branch, which converts a polytope guard to a conZonotope and
leaves the invariant alone, and the conversion of a non-polytope guard to a polytope.

## Inputs
* `e` – transition
* `inv` – invariant polytope

## Output
* transition with the guard intersected with the invariant
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {L : Type} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The transition with its polytope guard cut to the invariant `inv`. -/
def Transition.convGuard (e : Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    (inv : HPolytope 𝕋 (Vec 𝕋 n)) :
    Transition (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n :=
  { e with guard := HPolytope.intersection e.guard inv }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
